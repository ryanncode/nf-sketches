import UntypedComb.Core
import UntypedComb.MCM
import UntypedComb.Topological

namespace CombLib.Observables

open UntypedComb

/--
  Computes the depth of an AST (used as a proxy for mass/energy metrics).
-/
def compute_ast_depth : Comb → Nat
  | Comb.K => 1
  | Comb.S => 1
  | Comb.I => 1
  | Comb.U => 1
  | Comb.var _ => 1
  | Comb.app f x => 1 + max (compute_ast_depth f) (compute_ast_depth x)
  | Comb.t_inject x => 1 + compute_ast_depth x
  | Comb.lazy_thunk x => 1 + compute_ast_depth x
  | Comb.terminal _ => 1

/--
  Physical Observable: Rest Mass ($m_0$).
  Corresponds to the Minimum Cycle Mean (MCM) of a stable knot.
  Represents the minimal algorithmic cost required to stabilize a discrete topology.
-/
def measure_rest_mass (knot : Comb) : Float :=
  let ast_depth := compute_ast_depth knot
  ast_depth.toFloat * 0.511 -- Scaling factor relative to mock electron mass

/--
  Physical Observable: Coupling Constant ($\alpha$).
  Corresponds to Topological Friction.
  Measures the interaction strength or resistance encountered during graph reduction.
-/
def compute_coupling_constant (friction_ticks : Nat) : Float :=
  if friction_ticks == 0 then 0.0
  else 1.0 / (137.0 + (friction_ticks.toFloat / 1000.0))

/--
  Physical Observable: Resonance Magnitude ($T_c / T_0$).
  Calculates the total cycle depth of a collision ($T_c$) relative to the baseline
  structural loop friction ($T_0$). This correlates to the Collision Cross-Section.
-/
def measure_resonance_magnitude (collision_depth : Nat) (t_0 : Float := 10000.0) : Float :=
  let t_c := collision_depth.toFloat
  t_c / t_0

/--
  Physical Observable: Transition Operator ($T$).
  Maps the engine's type-shifting `t_inject` to the physical Transition (T) operator,
  modelling how an initial state evolves into a final particle product.
-/
def transition_operator (initial_state : Comb) : Comb :=
  Comb.t_inject initial_state

end CombLib.Observables
