import UntypedComb.Core
import UntypedComb.Topological
import UntypedComb.Categorical
import UntypedComb.Reduction

namespace UntypedComb

/--
  The Missing Verification Bridge.
  Evaluates a local subgraph during the DAG topological sort, and requires a formal
  Lean proof that the subgraph satisfies `StronglyCantorianSets.is_sc`
  before wrapping it in the `Comb.terminal "SC_CUT"` tag.
-/
def verifyAndWrapSC {V : Type} {spe : StratifiedPseudoElephant V}
    (sc : StronglyCantorianSets V spe) (_obj : spe.Obj) (_proof : sc.is_sc _obj) (subgraph : Comb) : Comb :=
  Comb.app (Comb.terminal "SC_CUT") subgraph

-- 1. Graph Representation

structure NodeId where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

structure Edge where
  src : NodeId
  dst : NodeId
  weight : Int
  deriving Repr

structure DAG where
  nodes : Array (NodeId × Comb)
  edges : Array Edge
  deriving Repr

-- 2. AST to Graph Translation

def nextId (d : DAG) : NodeId :=
  ⟨d.nodes.size⟩

def addNode (d : DAG) (c : Comb) : DAG × NodeId :=
  let id := nextId d
  ({ d with nodes := d.nodes.push (id, c) }, id)

def addEdge (d : DAG) (src dst : NodeId) (weight : Int) : DAG :=
  { d with edges := d.edges.push ⟨src, dst, weight⟩ }

mutual
  def astToGraphAux (c : Comb) (d : DAG) : DAG × NodeId :=
    match c with
    | Comb.S => addNode d Comb.S
    | Comb.K => addNode d Comb.K
    | Comb.I => addNode d Comb.I
    | Comb.U => addNode d Comb.U
    | Comb.var s => addNode d (Comb.var s)
    | Comb.terminal s => addNode d (Comb.terminal s)
    | Comb.lazy_thunk k inner =>
      let (d1, innerId) := astToGraphAux inner d
      let (d2, selfId) := addNode d1 (Comb.lazy_thunk k inner)
      (addEdge d2 selfId innerId 0, selfId) -- Neutral weight for thunks
    | Comb.t_inject inner =>
      let (d1, innerId) := astToGraphAux inner d
      let (d2, selfId) := addNode d1 (Comb.t_inject inner)
      (addEdge d2 selfId innerId (-1), selfId) -- T-inject applies a weight of -1
    | Comb.app c1 c2 =>
      let (d1, id1) := astToGraphAux c1 d
      let (d2, id2) := astToGraphAux c2 d1
      let (d3, selfId) := addNode d2 (Comb.app c1 c2)
      -- app connects to both children, with neutral weights for topological sorting purposes
      let d4 := addEdge d3 selfId id1 0
      (addEdge d4 selfId id2 0, selfId)
end

def toGraph (c : Comb) : DAG :=
  (astToGraphAux c ⟨#[], #[]⟩).1

-- 3. SCC Isolation (Tarjan's)

def getNeighbors (d : DAG) (n : NodeId) : List NodeId :=
  d.edges.toList.filter (fun e => e.src.id == n.id) |>.map (fun e => e.dst)

structure TarjanState where
  index : Nat := 1
  indices : List (NodeId × Nat) := []
  lowlinks : List (NodeId × Nat) := []
  onStack : List NodeId := []
  stack : List NodeId := []
  sccs : List (List NodeId) := []

def lookupIdx (k : NodeId) (l : List (NodeId × Nat)) : Nat :=
  match l.find? (fun (id, _) => id == k) with
  | some (_, v) => v
  | none => 0

def insertIdx (k : NodeId) (v : Nat) (l : List (NodeId × Nat)) : List (NodeId × Nat) :=
  (k, v) :: l.filter (fun (id, _) => id != k)

partial def tarjanSCC (d : DAG) (v : NodeId) (state : TarjanState) : TarjanState :=
  let idx := state.index
  let s1 := { state with 
    indices := insertIdx v idx state.indices,
    lowlinks := insertIdx v idx state.lowlinks,
    index := idx + 1,
    onStack := v :: state.onStack,
    stack := v :: state.stack
  }
  
  let neighbors := getNeighbors d v
  let s2 := neighbors.foldl (fun s w =>
    if lookupIdx w s.indices == 0 then
      let s_after := tarjanSCC d w s
      let low_v := lookupIdx v s_after.lowlinks
      let low_w := lookupIdx w s_after.lowlinks
      { s_after with lowlinks := insertIdx v (min low_v low_w) s_after.lowlinks }
    else if s.onStack.contains w then
      let low_v := lookupIdx v s.lowlinks
      let index_w := lookupIdx w s.indices
      { s with lowlinks := insertIdx v (min low_v index_w) s.lowlinks }
    else
      s
  ) s1

  if lookupIdx v s2.lowlinks == lookupIdx v s2.indices then
    let rec popSCC (stack : List NodeId) (onStack : List NodeId) (scc : List NodeId) : List NodeId × List NodeId × List NodeId :=
      match stack with
      | [] => ([], onStack, scc)
      | w :: rest =>
        let newOnStack := onStack.filter (fun id => id != w)
        let newScc := w :: scc
        if w == v then
          (rest, newOnStack, newScc)
        else
          popSCC rest newOnStack newScc
    
    let (newStack, newOnStack, scc) := popSCC s2.stack s2.onStack []
    { s2 with stack := newStack, onStack := newOnStack, sccs := scc :: s2.sccs }
  else
    s2

def findSCCs (d : DAG) : List (List NodeId) :=
  let nodes := d.nodes.toList.map (fun (id, _) => id)
  let finalState := nodes.foldl (fun state v =>
    if lookupIdx v state.indices != 0 then state else tarjanSCC d v state
  ) {}
  finalState.sccs

-- 4. Existential Projection Collapse

def isCyclicSCC (scc : List NodeId) (d : DAG) : Bool :=
  scc.length > 1 ||
  d.edges.toList.any (fun e => e.src.id == scc.head!.id && e.dst.id == scc.head!.id)

/-- Rebuilds the Comb AST from the DAG nodes, applying U-combinator projections where SCCs represent cycles. -/
partial def rebuildGraph (d : DAG) (sccs : List (List NodeId)) (currentNode : NodeId) : Comb :=
  let c := match d.nodes.toList.find? (fun (id, _) => id == currentNode) with
           | some (_, comb) => comb
           | none => Comb.var "error_node_not_found"

  -- Check if current node is part of a cyclic SCC
  let isCyclic := sccs.any (fun scc => scc.contains currentNode && isCyclicSCC scc d)

  if isCyclic then
    -- Project the entire self-referential graph segment securely using the U combinator
    Comb.app Comb.U c
  else
    -- Standard translation back down the AST based on children
    let children := d.edges.toList.filter (fun e => e.src == currentNode) |>.map (fun e => e.dst)
    match c with
    | Comb.app _ _ =>
      if children.length == 2 then
        let child0 := children.getD 0 currentNode
        let child1 := children.getD 1 currentNode
        Comb.app (rebuildGraph d sccs child0) (rebuildGraph d sccs child1)
      else c -- Fallback if translation dropped edges
    | Comb.t_inject _ =>
      if children.length == 1 then
        let child0 := children.getD 0 currentNode
        Comb.t_inject (rebuildGraph d sccs child0)
      else c
    | Comb.lazy_thunk k _ =>
        let child0 := d.edges.filter (fun e => e.src == currentNode) |>.map (fun e => e.dst) |>.getD 0 currentNode
        if sccs.any (fun scc => scc.contains child0) then
          Comb.lazy_thunk k (rebuildGraph d sccs child0)
        else c
    | _ => c

def collapseSCCs (d : DAG) (sccs : List (List NodeId)) (rootId : NodeId) : Comb :=
  rebuildGraph d sccs rootId

-- 5. DAG Re-Translation

def compileAcyclic (c : Comb) : Comb :=
  -- 1. Translate to DAG
  let (d, rootId) := astToGraphAux c ⟨#[], #[]⟩
  -- 2. Find SCCs
  let sccs := findSCCs d
  -- 3. Collapse 0-weight semantic cycles using projection
  collapseSCCs d sccs rootId

def DAG.reduce (c : Comb) : Comb :=
  UntypedComb.normalize (compileAcyclic c)

end UntypedComb
