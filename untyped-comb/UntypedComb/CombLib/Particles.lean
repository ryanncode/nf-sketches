import UntypedComb.Core
import UntypedComb.CombLib.CausalGraph
import UntypedComb.CombLib.Accelerator

namespace CombLib.Particles

open CombLib.Causal (causal_braid symmetric_node saturated_boundary)
open CombLib.Accelerator (base_particle)
open UntypedComb

/--
  The Electron Knot.
  A Strongly Cantorian (SC) island representing a stable soliton or trefoil-like subgraph.
  It achieves a stable ground state Minimum Cycle Mean (MCM).
-/
def electron_knot : Comb :=
  Comb.app (Comb.terminal "SC_CUT_ELECTRON") base_particle

/--
  The Nucleon Braid.
  A multi-stranded causal braid containing deeply nested, irreducible Symmetric Nodes
  that represent strongly-interacting quarks.
-/
def nucleon_braid : Comb :=
  let quark1 := symmetric_node base_particle base_particle
  let quark2 := symmetric_node base_particle base_particle
  let quark3 := symmetric_node base_particle base_particle
  let gluon_field := Comb.lazy_thunk (Comb.app causal_braid (Comb.app quark1 quark2))
  Comb.app gluon_field quark3

/--
  The Gauge Boson Wave.
  Transitory graph structures representing acoustic-like ripples of syntactic
  friction moving across the saturated boundary.
-/
def gauge_boson_wave : Comb :=
  Comb.lazy_thunk (Comb.app (Comb.t_inject causal_braid) saturated_boundary)

end CombLib.Particles
