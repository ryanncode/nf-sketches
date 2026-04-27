import UntypedComb.Core
import UntypedComb.Topological

namespace UntypedComb

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

-- 3. SCC Isolation (Kosaraju's)

def getNeighbors (d : DAG) (n : NodeId) : List NodeId :=
  d.edges.toList.filter (fun e => e.src.id == n.id) |>.map (fun e => e.dst)

def getReverseNeighbors (d : DAG) (n : NodeId) : List NodeId :=
  d.edges.toList.filter (fun e => e.dst.id == n.id) |>.map (fun e => e.src)

partial def dfsForward (d : DAG) (n : NodeId) (visited : List NodeId) (order : List NodeId) : List NodeId × List NodeId :=
  if visited.contains n then (visited, order)
  else
    let neighbors := getNeighbors d n
    let (v1, o1) := neighbors.foldl (fun (v, o) curr =>
      dfsForward d curr v o
    ) (n :: visited, order)
    (v1, n :: o1)

partial def dfsBackward (d : DAG) (n : NodeId) (visited : List NodeId) (scc : List NodeId) : List NodeId × List NodeId :=
  if visited.contains n then (visited, scc)
  else
    let neighbors := getReverseNeighbors d n
    let (v1, scc1) := neighbors.foldl (fun (v, s) curr =>
      dfsBackward d curr v s
    ) (n :: visited, n :: scc)
    (v1, scc1)

def findSCCs (d : DAG) : List (List NodeId) :=
  let (_, order) := d.nodes.toList.foldl (fun (v, o) (id, _) =>
    if v.contains id then (v, o) else dfsForward d id v o
  ) ([], [])

  let (_, sccs) := order.foldl (fun (v, sccs) id =>
    if v.contains id then (v, sccs)
    else
      let (v1, scc) := dfsBackward d id v []
      (v1, scc :: sccs)
  ) ([], [])
  sccs

-- 4. Existential Projection Collapse

def isCyclicSCC (scc : List NodeId) (d : DAG) : Bool :=
  scc.length > 1 ||
  d.edges.toList.any (fun e => e.src.id == scc.head!.id && e.dst.id == scc.head!.id)

def collapseSCCs (c : Comb) : Comb :=
  -- Real graph flattening implementation would project the specific subset of the DAG.
  -- For now, if we encounter a non-well-founded recursive app like (x x) we can trap it in a U combinator.
  c

-- 5. DAG Re-Translation

def compileAcyclic (c : Comb) : Comb :=
  -- 1. Translate to DAG
  let _d := toGraph c
  -- 2. Find SCCs
  -- let sccs := findSCCs d
  -- 3. Collapse 0-weight semantic cycles
  collapseSCCs c

end UntypedComb
