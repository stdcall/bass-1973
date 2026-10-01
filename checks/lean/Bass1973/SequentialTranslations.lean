import Mathlib.Algebra.Group.Defs

/-!
# Two algebraic steps for sequential translation categories

Bass, *Algebraic K-Theory*, I (8.6), Russian edition Mir 1973, p.55,
`prop:sequential-cofinal-translations`.

The first equality gives the missing arrow of the cofinality square:
the book's `s_n+b=a`, `b+c=a_(n,m)` and `s_n+a_(n,m)=s_m` imply
`a+c=s_m`. The second shows how adding a later transition equalizes
parallel arrows in a commutative monoid; no cancellation is assumed.

Only these algebraic equalities are proved. The construction of the
index category, the existence condition(S), the counterexample to the
printed subcategory, and the general colimit theorem are not formalized.
-/

namespace Bass1973

theorem sequential_cofinal_square {M : Type*} [AddMonoid M]
    (sₙ b a c transition sₘ : M)
    (ha : sₙ + b = a) (hc : b + c = transition)
    (hs : sₙ + transition = sₘ) : a + c = sₘ := by
  calc
    a + c = (sₙ + b) + c := by rw [ha]
    _ = sₙ + (b + c) := add_assoc _ _ _
    _ = sₙ + transition := by rw [hc]
    _ = sₘ := hs

theorem translations_parallel_equalized {M : Type*} [AddCommMonoid M]
    (t b₁ b₂ s d transition : M)
    (h₁ : t + b₁ = s) (h₂ : t + b₂ = s)
    (ht : transition = t + d) : b₁ + transition = b₂ + transition := by
  rw [ht]
  calc
    b₁ + (t + d) = (t + b₁) + d :=
      (add_assoc b₁ t d).symm.trans (congrArg (fun x => x + d) (add_comm b₁ t))
    _ = s + d := by rw [h₁]
    _ = (t + b₂) + d := by rw [h₂]
    _ = b₂ + (t + d) :=
      (congrArg (fun x => x + d) (add_comm t b₂)).trans (add_assoc b₂ t d)

#print axioms sequential_cofinal_square
#print axioms translations_parallel_equalized

end Bass1973
