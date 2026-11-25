import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10264

def circ : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [19]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 20]⟩], 21⟩

lemma fanin : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma correct : ∀ x : Fin 6 → Bool, circ.eval (List.ofFn x) = (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 2) x := by
  decide

end PEqualNP.Outside.L_meta_10264

theorem PEqualNP.Outside.L_meta_10264 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 2) 16 :=
  ⟨PEqualNP.Outside.L_meta_10264.circ, PEqualNP.Outside.L_meta_10264.fanin, by decide, PEqualNP.Outside.L_meta_10264.correct⟩
