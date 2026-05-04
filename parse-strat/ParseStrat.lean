import NfValidate
import ParseStrat.ITP

/-!
# ParseStrat: Shared Library and Formatting Tools

This module serves as the root of the `ParseStrat` library, providing shared
formatting and diagnostic helper functions that translate the internal
numerical evaluation results of `nf-validate` back into readable algebraic
proofs and type contradiction paths.
-/

--------------------------------------------------------------------------------
-- 1. VARIABLE AND WITNESS FORMATTING
--------------------------------------------------------------------------------
-- Basic string conversion for variables and the successful stratification
-- witness context.

def formatWitness (w : StratificationWitness) : String :=
  let flattened : List (ScopedVar × Int) := w.foldl (fun acc (s, l) => acc ++ l.map (fun (v, weight) => ((v, s), weight))) []
  let pairs := flattened.map (fun (v, l) => s!"{scopedVarToString v} : {l}")
  "{" ++ String.intercalate ", " pairs ++ "}"

--------------------------------------------------------------------------------
-- 2. CYCLE PATH RECONSTRUCTION & FORMATTING
--------------------------------------------------------------------------------
-- Translates the raw nodes and edges returned by the Bellman-Ford failure
-- case into a human-readable algebraic contradiction path.

/--
Reconstructs the detailed path string from a given cycle and list of edges.
It dynamically calculates the total algebraic contradiction weight and formats
the output to explicitly demonstrate the unstratifiable nature of the cycle.
-/
def formatDetailedCycleSandbox (c : List ScopedVar) (edges : List Edge) : String :=
  formatDetailedCycle c edges
