import Mathlib.Tactic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Digits --to do calculation ex.: succ = +1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Group.Basic
import Mathlib.Init.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics




namespace ostrowski
open NNReal

section AbsoluteValue

--section Preliminaries

#check MulRingNorm

--We use the definition of absolute value from Mathlib



--We define the real norm on Q using the one from R
instance my_abs_real :  MulRingNorm ℚ:=
{ toFun :=norm
  map_zero':= by simp only [norm_zero]
  add_le':= by exact fun r s => norm_add_le r s
  eq_zero_of_map_eq_zero':= by simp only [norm_eq_zero, imp_self, forall_const]
  map_mul':= by simp only [norm_mul, forall_const]
  neg':= by simp only [norm_neg, forall_const]
  map_one':= by simp only [norm_one]
}

#eval my_abs_real (-6)
#check my_abs_real.add_le'

#check Nat.Prime


-- Real.ratCast is for Q inside R
variable {np: ℚ → ℝ }
instance my_abs_padic (p:ℕ ) (hp : Nat.Prime p) : MulRingNorm ℚ :=
{ toFun := fun x : ℚ => (padicNorm p x: ℝ)
  map_zero' := by simp only [ne_eq, padicNorm.zero, Rat.cast_zero]
  add_le'   := sorry,
  neg'      := sorry,
  eq_zero_of_map_eq_zero' := sorry,
  map_one' := sorry,
  map_mul' := sorry,
}

#print my_abs_padic

#check (2:ℝ)^3


-- Trivial Absolute Valure:
/-
def my_abs_triv : MulRingNorm ℚ :=
{ toFun := λ x : ℚ => (if x=0 then (0 : ℝ)  else 1 : ℝ)
  map_zero' := by sorry,
  add_le'   := by sorry,
  neg'      := sorry,
  eq_zero_of_map_eq_zero' := sorry,
  map_one' := sorry,
  map_mul' := sorry,

#eval my_abs_triv (0)
#eval my_abs_triv (42)
#eval my_abs_triv (-37/8)
-/


def my_equiv {R : Type*} [Ring R] (f: MulRingNorm R) (g : MulRingNorm R) := ∃  c: ℝ , c >0 ∧ (∀x : R,  (f x)^c= g x)
#check my_equiv

--instance my_equiv : equivalence

lemma my_equiv_refl {R : Type*} [Ring R] (f : MulRingNorm R) :
  my_equiv f f := by



  use 1

  simp only [gt_iff_lt, zero_lt_one]
  simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Real.rpow_one, forall_const, and_self]

/-

In the proof for Lean 3 they used

 -- refine ⟨1, by linarith, by simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Real.rpow_one,forall_const]⟩

where \langle 1 is taking c=1, and then proof c >0 ∧ (∀x : R,  (f x)^c= g x)
the fist part is done using linarith solves the inequality
and the other part is solved using the propertis of the norm


-/

lemma equiv_symm {R : Type*} [Ring R] (f g : MulRingNorm R) (fg : my_equiv f g) :
  my_equiv g f :=by
  rcases fg with ⟨c, fg1, fg2⟩
  use 1/c
  apply And.intro
  · rw[ one_div, gt_iff_lt, ← inv_pos, inv_inv, ← gt_iff_lt]
    exact fg1
  · intro x
    rw[← fg2, ← Real.rpow_mul, @mul_one_div]
    have h1 : c ≠ 0 := by linarith
    simp [h1]
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_nonneg]
  done



lemma equiv_trans {R : Type*} [Ring R] (f g l : MulRingNorm R) (fg : my_equiv f g) (gl : my_equiv g l) :
my_equiv f l :=by
  rcases fg with ⟨c, fg1, fg2⟩
  rcases gl with ⟨d, gl1, gl2⟩
  use c*d
  apply And.intro
  · exact Real.mul_pos fg1 gl1
  · intro x
    rw [Real.rpow_mul]
    rw [ ← gl2, ← fg2]
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_nonneg]
  done




-----------------------------------------------------------------------------------------------------------------------
--Now we extend the norm form N to Q
lemma my_f_rat (f : MulRingNorm ℚ) (a: ℤ)(b: ℕ )(no: b ≠ 0): f (a / b) = (f a) /(f b):= by
have no' : f b ≠ 0 := by{
  simp[f.eq_zero_of_map_eq_zero']
  exact no }
refine (eq_div_iff no').mpr ?_
rw[← f.map_mul']
have eq:  a / b * b = (a:ℚ ) := by{
refine (div_eq_iff_mul_eq ?hb).mp rfl
exact Nat.cast_ne_zero.mpr no}
rw[eq]
done

--probably is avaliable but I wasn't able to find it
lemma my_abs_eq_abs.norm (f : MulRingNorm ℚ)(x : ℤ ) : f x = f (Int.natAbs x) :=by
by_cases x≥ 0
· have aux1 :  Int.natAbs x = x :=by {
  simp only [Int.coe_natAbs, abs_eq_self]
  exact h
}
  exact congrArg f.toFun (congrArg Int.cast (id aux1.symm))
· have aux2 :  Int.natAbs x = -x :=by {
  simp only [Int.coe_natAbs, abs_eq_neg_self]
  rw [@Int.not_le] at h
  exact Int.le_of_lt h
}
  rw[← f.neg', ← Rat.intCast_neg]
  exact congrArg f.toFun (congrArg Int.cast (id aux2.symm))

--to find the lemma
lemma help_me1 (f : MulRingNorm ℚ)(x y : ℤ)(h: x=y): f x= f y :=by
exact congrArg f.toFun (congrArg Int.cast h)

lemma my_nat_ext  (f g : MulRingNorm ℚ) (h : ∀n:ℕ, f n = g n) : f=g :=by
ext x
by_cases h1 : x=0
· simp only [h1, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_zero]
· rw [← Rat.num_div_den x] --write as a division of integers
  rw [my_f_rat, my_f_rat]
  · have h_den : f x.den = g x.den :=by {exact h x.den}
    rw[h_den]
    rw[div_left_inj']
    · rw[my_abs_eq_abs.norm, my_abs_eq_abs.norm]
      exact h (Int.natAbs x.num)

    · simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, ne_eq, map_eq_zero, Nat.cast_eq_zero]
      exact x.den_nz
  · exact x.den_nz
  · exact x.den_nz
done

--to find the right lemmas
lemma my_div_inj (a b c: ℝ  )(no: a ≠ 0): b / a =  c/a ↔ b=c:= by
exact div_left_inj' no
done


section NonArchimedean


-- Non Archimedean propriety most general case, the class Add is used to say Lean that A has an Addition, similar for Lienar Order
def my_nonarchimedean {A : Type*} [Add A] {B : Type*} [LinearOrder B] (f : A → B) : Prop :=
∀ r s, f (r + s) ≤ max (f r) (f s)

-- I don't get it ahahah
/-
lemma my_nonarchimedean_def {A : Type*} [Add A] {B : Type*} [LinearOrder B] (f : A → B) :
my_nonarchimedean f ↔ ∀ r s, f (r + s) ≤ max (f r) (f s) :=by exact Iff.rfl
-/



-- Know we what to prove that every Non Archimedean abs is a p-adic abs


variable {f : MulRingNorm ℚ}

#check map_one f


-- We start proving that a Non Archimedean abs is bounded over Z. We done it before on N so that we can use the indution:
lemma my_bounded_N (h : my_nonarchimedean f) (n : ℕ) :  f n ≤1 :=by
induction n with
| zero => simp only [Nat.zero_eq, CharP.cast_eq_zero, AddGroupSeminorm.toFun_eq_coe, map_zero, zero_le_one]
| succ n ih =>
rw [Nat.succ_eq_add_one]
specialize h n 1
simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_one, ge_iff_le] at h
simp only [Nat.cast_add, Nat.cast_one]
rw[AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe] at ih
apply le_trans h (max_le ih rfl.ge)
-- short way to say apply the transitivity giving the to prove directly in the funtion (max_le is the prove that if a< c and b< c the max a c < c)


done

lemma my_bounded_Z (h : my_nonarchimedean f) (n : ℤ ) :  f n ≤1 :=by
cases n
· apply my_bounded_N (h)
· simp only [Int.cast_negSucc]
  rw[f.neg']
  apply my_bounded_N (h)
done


-----------------------------------------------------------------------------------------------------------------



--Now we want to prove that exist a prime such that fp<1
--In order to do this we will use the following lemma that is an
--induction on prime for multiplicative proprieties
lemma dvd_induction {P : ℕ → Prop} (n : ℕ)
    (P0 : P 0)
    (P1 : P 1)
    (P_mul : ∀ {p a}, Nat.Prime p → a ≠ 0 → a ≠ 1 → P a → P (p * a))
    (P_prime : ∀ {p}, Nat.Prime p → P p) :
    P n := by
  apply Nat.strongInductionOn
  intros n hn
  by_cases h : n ≤ 1
  · interval_cases n <;> assumption
  · have := Nat.exists_prime_and_dvd (ne_of_not_le h)
    rcases this with ⟨p, pPrime, ⟨q, rfl⟩⟩
    rcases q with _ | _ | q
    · simpa
    · simp [P_prime pPrime]
    · apply P_mul pPrime (Nat.succ_ne_zero _) q.succ_succ_ne_one
      · apply hn
        apply (one_mul _).symm.le.trans_lt
        apply Nat.mul_lt_mul_of_pos_right pPrime.one_lt
        exact Nat.succ_pos _
  done




-- Exist a natural number such that fn <1
lemma my_ex_n (h : my_nonarchimedean f) (h1 : f ≠ 1) : ∃n:ℕ, (n≠0)∧ f n < 1 :=by
revert h1
contrapose!
intro h2
--by_contra' h2
simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe] at h2

have eq (x : ℕ)(no_z : x≠0): 1 = f x :=by{
  have le:  1 ≤ f x :=by{
    exact h2 x no_z
  }
  have ge:   f x ≤ 1 :=by{
    exact my_bounded_N h x
    }
  exact le_antisymm le ge
}
apply my_nat_ext
intro n
by_cases n=0
· rw[h]
  simp only [CharP.cast_eq_zero, AddGroupSeminorm.toFun_eq_coe, map_zero, MulRingNorm.apply_one, ite_true]
· rw [← @ne_eq] at h
  simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, MulRingNorm.apply_one]
  aesop
  exact (Real.ext_cauchy (congrArg Real.cauchy (eq n h))).symm
done

--finally we prove the existence of a prime p such that fp<1
lemma my_ex_p (h : my_nonarchimedean f) (h1 : f ≠ 1) : ∃p:ℕ,  ( Nat.Prime p) ∧ f p < 1 :=by
revert h1
contrapose!
intro h2
have eq (x : ℕ)(hx : Nat.Prime x): 1 = f x :=by{
  have le:  1 ≤ f x :=by{
    exact h2 x hx
  }
  have ge:   f x ≤ 1 :=by{
    exact my_bounded_N h x
    }
  exact le_antisymm le ge
}
apply my_nat_ext
intro n
apply dvd_induction n
· simp only [CharP.cast_eq_zero, AddGroupSeminorm.toFun_eq_coe, map_zero]
· simp only [Nat.cast_one, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_one]
· intro p a hp na0 na1 eq_a
  simp only [Nat.cast_mul, map_mul]
  simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_mul]
  simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe] at eq_a
  rw[eq_a]
  simp only [mul_eq_mul_right_iff, map_eq_zero, Nat.cast_eq_zero]
  aesop
  simp only [← AddGroupSeminorm.toFun_eq_coe,←  MulRingSeminorm.toFun_eq_coe]
  simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, MulRingNorm.apply_one, Nat.cast_eq_zero]
  aesop
  exact (Real.ext_cauchy (congrArg Real.cauchy (eq p hp))).symm
· intro p hp
  simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, MulRingNorm.apply_one, Nat.cast_eq_zero]
  have p_not_0: p≠0 :=by exact Nat.Prime.ne_zero hp
  aesop
  exact (Real.ext_cauchy (congrArg Real.cauchy (eq p hp))).symm
done

------------------------------------------------------------------------------------------------------------------
#check Ideal
#check Ideal ℤ
--Now prove that {x : ℤ | f x < 1} is an ideal of Z
def I (h : my_nonarchimedean f) : Ideal ℤ :=
{ carrier := {x : ℤ | f x < 1}
  add_mem' := by {
    intro x y hx hy
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Set.mem_setOf_eq, Int.cast_add, map_mul]  at hx hy ⊢
    calc
    f (x+y) ≤ max (f x) (f y) :=by {exact h ↑x ↑y}
    _ < 1 := by{ exact max_lt hx hy}
    }

  zero_mem':= by {simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Set.mem_setOf_eq,
    Int.cast_zero, map_zero, zero_lt_one]}
  smul_mem':= by {
    intro x y hy
    simp only [smul_eq_mul, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Set.mem_setOf_eq, Int.cast_mul,
      map_mul] at hy ⊢
    have aux : f x≤ 1:=by { exact my_bounded_Z h x}
    calc
    f x*f y ≤  f y := by {
      simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, gt_iff_lt]
      refine mul_le_of_le_one_left ?hb aux
      exact map_nonneg f.toMulRingSeminorm ↑y
    }
    f y < 1 := by{exact hy}
  }
}
#check I


--Now we want to prove that thi ideal is prime. In order to do that we prove that is proper and contais a prime ideal.
--Proper:
lemma my_I_proper (h : my_nonarchimedean f) : I h ≠ (⊤ : Ideal ℤ) :=by
rw [@Ideal.ne_top_iff_one]
unfold I
simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Submodule.mem_mk, AddSubmonoid.mem_mk,
  AddSubsemigroup.mem_mk, Set.mem_setOf_eq, Int.cast_one, map_one, lt_self_iff_false, not_false_eq_true]
done

--Contain a prime ideal:
lemma my_I_cont_prime (h : my_nonarchimedean f) (h1 : f ≠ 1) :
∃p:ℕ,  ( Nat.Prime p) ∧  I h ≥ Ideal.span {(p:ℤ)}:=by
obtain ⟨p, hp⟩ := my_ex_p h h1
aesop
use p
refine (and_iff_left ?h.hb).mpr left
rw [@Ideal.span_singleton_le_iff_mem]
unfold I
simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Submodule.mem_mk, AddSubmonoid.mem_mk,
  AddSubsemigroup.mem_mk, Set.mem_setOf_eq, Int.cast_ofNat]
exact right
done

--Prime:
lemma I_prime (h : my_nonarchimedean f) (h1 : f ≠ 1) :
  ∃ (p : ℕ),  ( Nat.Prime p) ∧  I h = Ideal.span {(p:ℤ)} :=by
obtain ⟨p, hp⟩ := my_I_cont_prime h h1
use p
apply And.intro
·exact And.left hp
· refine (Ideal.IsMaximal.eq_of_le ?h.right.hI ?h.right.hJ ?h.right.IJ).symm
  · refine Ideal.IsPrime.isMaximal ?h.right.hI.h ?h.right.hI.hp
    · rw[Ideal.span_singleton_prime,@Int.prime_iff_natAbs_prime]
      rw [Int.natAbs_cast]
      ·exact hp.left
      ·aesop
    · simp only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
      aesop
  · exact my_I_proper h
  · exact And.right hp
done

----------------------------------------------------------------------------------------------------------

--
variable (p:ℕ )
#check Fact (Nat.Prime p)









lemma mult_finite {a : ℤ} {p : ℕ} (hp : Nat.Prime p) (ha : a ≠ 0) :
  (multiplicity.Finite (p : ℤ) a) :=by
apply multiplicity.finite_int_iff.mpr
simp only [ha, hp.ne_one, Int.natAbs_ofNat, Ne.def, not_false_iff, and_self]
done




-- padic abs in function of padic valuation:
lemma my_padicabs_eq_p_pow_padicval (p : ℕ) (hp: Nat.Prime p) {q : ℚ} (hq : q ≠ 0) : (my_abs_padic p hp q) = p ^ (-padicValRat p q) :=by
unfold my_abs_padic
simp only [ne_eq]
rw[padicNorm.eq_zpow_of_nonzero hq]
norm_cast
rw [@Rat.cast_zpow, @Rat.cast_coe_nat]
done



--this if for sure avaliable but i wasn't able to find it
lemma help_me11 (x y z:ℝ) (h: x >0) : (x^y)^z=(x^z)^y :=by
rw[← Real.rpow_mul,← Real.rpow_mul]
· rw[mul_comm]
· exact le_of_lt h
· exact le_of_lt h
done







#check (∃ p:ℕ,  (Nat.Prime p) ∧ (∃ s : ℝ,   (s > 0) ∧ ∀ (x : ℤ), f x = (my_abs_padic p _ x)^s))


lemma my_p_val_Z2 (h' : my_nonarchimedean f) (h1 : f ≠ 1) :
(∃ p:ℕ,  (Nat.Prime p)∧ ((hp: Nat.Prime p) → (∃ s : ℝ,   (s > 0) ∧ ∀ (x : ℤ), f x = (my_abs_padic p hp x)^s))) :=by
obtain ⟨p, hp⟩ := I_prime h' h1
use p
have fra :  Real.logb (↑p) (f ↑p)<0:=by{
  simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, gt_iff_lt]
  aesop
  have aux1 : I h' ≥ Ideal.span {↑p} :=by{
    exact Eq.le (id right.symm)
    }
  have aux2 : f p<1 :=by{
    simp [Ideal.span_singleton_le_iff_mem] at aux1
    unfold I at aux1
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq, Int.cast_ofNat] at aux1
    exact aux1
  }
  calc
  0=Real.logb (↑p) (1) :=by exact Real.logb_one.symm
  _ > Real.logb (↑p) (f ↑p) :=by{
    apply  Real.logb_lt_logb
    · simp only [Nat.one_lt_cast]
      exact Nat.Prime.one_lt left
    · simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
      rw [@lt_iff_le_and_ne]
      simp only [map_nonneg, ne_eq, true_and]
      rw [← @ne_eq, @ne_comm, @map_ne_zero]
      have aux3: p≠0:=by {exact Nat.Prime.ne_zero left}
      exact Nat.cast_ne_zero.mpr aux3
    · exact aux2
  }
}

apply And.intro
· exact hp.left
· intro hp'
  use -Real.logb p (f p)
  apply And.intro
  · exact neg_pos.mpr fra
  · intro x
    by_cases x=0
    · rw [Mathlib.Tactic.Qify.int_cast_eq] at h
      rw [h]
      simp only [Int.cast_zero, AddGroupSeminorm.toFun_eq_coe, map_zero, MulRingSeminorm.toFun_eq_coe, ne_eq,
        Real.logb_eq_zero, Nat.cast_eq_zero, Nat.cast_eq_one, map_eq_zero]
      simp only [← AddGroupSeminorm.toFun_eq_coe, ← MulRingSeminorm.toFun_eq_coe]
      rw[Real.zero_rpow]
      apply ne_of_gt ?_
      exact neg_pos.mpr fra
    · let m := (multiplicity (p : ℤ) x).get (mult_finite hp.left h)
      have : f x = (f p) ^ m:=by{
        simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Real.rpow_nat_cast]
        obtain ⟨b, h_factor, h_b_coprime⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd (mult_finite hp.left h)
        rw [Mathlib.Tactic.Qify.int_cast_eq] at h_factor
        rw[h_factor]
        simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, map_mul, map_pow, ne_eq]
        have aux : f b =1:=by{
          have aux1 : b ∉ I h':=by{
          rw[hp.right]
          rw [@Ideal.mem_span_singleton]
          exact h_b_coprime
          }
          unfold I at aux1
          simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Submodule.mem_mk, AddSubmonoid.mem_mk,
            AddSubsemigroup.mem_mk, Set.mem_setOf_eq, not_lt] at aux1
          simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
          have aux2 : f b≤ 1:=by{
            exact my_bounded_Z h' b
          }
          simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe] at aux2
          linarith
        }
        aesop
        }
      rw [this]
      simp only [h]
      rw[my_padicabs_eq_p_pow_padicval]
      simp only [Ne.def,
      Int.cast_eq_zero, not_false_iff, padicValRat.of_int, zpow_neg, zpow_coe_nat,
      Rat.cast_inv, Rat.cast_pow, Rat.cast_coe_nat]
      /-
      simp only [h, padicNorm.eq_zpow_of_nonzero, Ne.def,
      Int.cast_eq_zero, not_false_iff, padicValRat.of_int, zpow_neg, zpow_coe_nat,
      Rat.cast_inv, Rat.cast_pow, Rat.cast_coe_nat]
      -/
      unfold padicValInt padicValNat
      simp [h, hp.left.ne_one, multiplicity.Int.natAbs p x]
      · have p_pos : (p : ℝ) > 0 :=by{
        simp only [Nat.cast_pos]
        apply Nat.Prime.pos hp.left
      }
        rw[help_me11 ↑p _ _ p_pos]
        have aux2: ↑p^ (Real.logb (↑p) (f ↑p))= (f ↑p):=by{
          norm_cast
          rw[Real.rpow_logb_eq_abs]
          aesop
          · exact p_pos
          · norm_cast
            exact Nat.Prime.ne_one hp.left
          · simp [@map_ne_zero]
            exact Nat.Prime.ne_zero hp.left
        }
        have aux2: ↑p^ (-Real.logb (↑p) (f ↑p))= (f ↑p)⁻¹:=by{
          rw[Real.rpow_neg]
          nth_rw 2 [← aux2]
          exact Nat.cast_nonneg p
        }
        aesop
        rw[← Real.rpow_neg_one]
        rw[← Real.rpow_mul]
        simp only [mul_neg, neg_mul, one_mul, neg_neg, Real.rpow_nat_cast]
        · exact map_nonneg f.toMulRingSeminorm ↑p






      · exact Rat.num_ne_zero.mp h












#check (∃ (p : ℕ),   (Nat.Prime p) ∧ (∃ s : ℝ,   (s > 0) ∧ ∀ (x : ℤ), f x = (my_abs_padic p _ x)^s))



lemma my_p_val_Q  (h' : my_nonarchimedean f) (h1 : f ≠ 1) :
(∃ (p : ℕ),   (Nat.Prime p) ∧ ((hp: Nat.Prime p) →  (∃ s : ℝ,   (s > 0) ∧ ∀ (x : ℚ), f x = (my_abs_padic p hp x)^s))) :=by
obtain ⟨p, hp⟩ := my_p_val_Z2 h' h1
aesop
specialize right left
use p
refine (and_iff_right left).mpr ?h.a
aesop
use w
refine (and_iff_left ?h.hb).mpr left_1
intro x
--from here I basically copy my proof of "my_nat_ext"
by_cases h: x=0
· rw[h, map_zero, map_zero]
  rw[Real.zero_rpow]
  exact ne_of_gt left_1
· rw [← Rat.num_div_den x]
  simp only [map_div₀]
  rw[Real.div_rpow]
  rw [right]
  · exact congrArg (HDiv.hDiv ((my_abs_padic p left).toMulRingSeminorm ↑x.num ^ w)) (right ↑x.den)
  · exact map_nonneg (my_abs_padic p (sorryAx (Nat.Prime p) true)).toMulRingSeminorm ↑x.num
  · exact map_nonneg (my_abs_padic p (sorryAx (Nat.Prime p) true)).toMulRingSeminorm ↑x.den
done



--find some lemmas
lemma help_me3 (x y w:ℝ) (h: x ≥  0)(h': y ≥  0) : (x/y)^w=x^w/y^w :=by
exact Real.div_rpow h h' w
done

--------------------------------------------------------------------------------------------------------------------------------
--f is a p-adic abs:
-- Finish: hence f and padic are equivalent
lemma my_f_padic (h : my_nonarchimedean f) (h1 : f ≠ 1) : ∃ (p : ℕ), (Nat.Prime p) ∧ ((hp:Nat.Prime p) → (my_equiv (my_abs_padic p hp) f )) :=by
obtain ⟨p, hp⟩ := my_p_val_Q h h1
aesop
use p
apply And.intro
· exact left
· unfold my_equiv
  intro hp'
  specialize right left
  simp_all only [gt_iff_lt, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
  unhygienic with_reducible aesop_destruct_products
  simp_all only
  apply Exists.intro
  apply And.intro
  on_goal 2 => intro x
  on_goal 2 => apply Eq.refl
  simp_all only

  /-
  --use s
  apply And.intro
  · exact hs
  · simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe] at h'
    intro x
    specialize h' x
    exact id h'.symm
done
-/
-- MAYO

-- this is just to find the result and it is faster to use
lemma my_f_nneg {x : ℚ  }: 0 ≤  f x:= by
  simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
  exact map_nonneg f.toMulRingSeminorm x

  done


--this is useful later
lemma my_f_pos {x : ℚ }(hn:  0 ≠ x ): 0 < f x:= by
  simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
  have h1:   0 ≠ f x  ↔  0 ≠ x :=by{
    rw [@not_iff_not]
    constructor
    · exact fun a => (MulRingNorm.eq_zero_of_map_eq_zero' f x (id a.symm)).symm
    · exact fun a => (hn (id a)).elim
  }
  refine Ne.lt_of_le ?_ (map_nonneg f.toMulRingSeminorm x)
  exact h1.mpr hn
  done


lemma my_f_ge1 {x: ℕ  }(le : ∃ n : ℕ, 1 < f n)(hn:  1 < x ): 1 ≤  f x:= by
  have le' := Nat.find_spec le
  sorry

-- it is just map_pow, so it is not really necessary
lemma my_pow_eq_pow {a : ℚ} {n : ℕ} : f (a ^ n) = (f a) ^ n := by
  induction n with
  | zero => simp only [Nat.zero_eq, pow_zero, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_one, CharP.cast_eq_zero, Real.rpow_zero]
  | succ n ih =>{
    rw [@pow_succ]
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_mul, map_pow, Nat.cast_succ]
    }






open BigOperators
open Real Filter Asymptotics

-- Two limits that we are going to use

lemma my_limit1 {N : ℝ} (hN : 0 < N) : Filter.Tendsto (λ n : ℕ => N ^ ((n : ℝ)⁻¹ )) Filter.atTop (nhds 1) := by
  rw[← Real.exp_log hN ]
  simp[ ← Real.exp_mul]
  have hey : Filter.Tendsto (λ n : ℕ => (Real.log N * (↑n)⁻¹)) Filter.atTop (nhds 0):= by{
    exact _root_.tendsto_const_div_atTop_nhds_0_nat (Real.log N)}
  refine Real.tendsto_exp_nhds_0_nhds_1.comp hey
  done



lemma my_limit2 {c : ℝ} (hc : 0 < c): Filter.Tendsto (λ n : ℕ => (1 + c*(n : ℝ))^((n : ℝ)⁻¹)) Filter.atTop (nhds 1) :=by
  -- have cne : c ≠ 0 := by{ exact ne_of_gt hc}
  have cne0 : c ≠ 0 := ne_of_gt hc
  have hey: (λ n : ℕ => (1+c*(n : ℝ))^((n : ℝ)⁻¹))  = (λ (x : ℝ  ) =>  (x ^ (1 / ((1 / c) * x  + (- 1) / c)))) ∘ (λ y : ℝ => 1 + c*y) ∘ (λ m :ℕ => (m:ℝ ) ):=by{
    ext n
    simp
    rw[mul_add, ← mul_assoc, mul_one,div_eq_mul_inv, add_comm c⁻¹,add_assoc,neg_mul, one_mul, add_right_neg, add_zero, inv_mul_cancel cne0, one_mul, mul_comm]
    }

  rw[hey]
  have : 1 / c ≠ 0 := one_div_ne_zero cne0
  refine (tendsto_rpow_div_mul_add 1 (1 / c) (-1 / c) (this.symm)).comp ?_

  apply Filter.tendsto_atTop_add_const_left
  apply Filter.Tendsto.const_mul_atTop hc
  intros x hx
  apply tendsto_nat_cast_atTop_atTop
  exact hx
  done
/-
In order to prove  that f is non archimedean if and only if it is bounded for all integers we need some lemmas. The first implication is rather easy whereas for the reciprocal we need to prove a chain of inequalities so as to then take a certain limit.
-/


/- Inequality that is later used -/

lemma my_ineq1 {a b : ℝ} (m: ℕ )(n : ℕ) (ha : 0 ≤  a) (hb : 0 ≤  b) : a^(m: ℝ)  * b^(n:ℝ ) ≤ max a b ^ (m + n :ℝ ) := by

rw[Real.rpow_add_of_nonneg]


have h: a^(m:ℝ )  ≤ (max a b)^(m:ℝ) :=by{
  refine Real.rpow_le_rpow ha (le_max_left a b ) (Nat.cast_nonneg m)}

have ht: b^(n:ℝ )  ≤ (max a b)^(n:ℝ) :=by{
refine Real.rpow_le_rpow hb (le_max_right a b ) (Nat.cast_nonneg n)}

have ha': 0 ≤ a^(m:ℝ )  :=by{exact Real.rpow_nonneg_of_nonneg ha ↑m }
have hb': 0 ≤  b^(n:ℝ ) :=by{exact Real.rpow_nonneg_of_nonneg hb ↑n }

refine mul_le_mul h ht hb' ?b0
exact le_trans ha' h

exact le_max_of_le_left ha
simp
simp
done


--This lemma solves a problem with a instance to apply triangule inequality in a easier way
lemma my_f_is_absval :IsAbsoluteValue f.toFun :=by
    refine { abv_nonneg' := ?abv_nonneg', abv_eq_zero' := ?abv_eq_zero', abv_add' := ?abv_add', abv_mul' := ?abv_mul' }
    · intros x
      simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_nonneg]
    · intro x
      constructor
      · exact fun a => MulRingNorm.eq_zero_of_map_eq_zero' f x a
      · simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_eq_zero, imp_self]
    · exact fun x y => AddGroupSeminorm.add_le' f.toAddGroupSeminorm x y
    · exact fun x y => MulRingSeminorm.map_mul' f.toMulRingSeminorm x y




/- The proof of this lemma contains the chain of inequalities mentioned above and is then used to formalise a slightly different version that is the one that we need for the result we are aiming for-/



lemma my_max_ineq' (n : ℕ) (x y : ℚ) (hf : ∀ m : ℕ, f m ≤ 1) :
  f (x + y)^(n : ℝ) ≤ (n + 1 : ℝ) * (max (f x) (f y) )^n := by

  norm_num
  rw [← @map_pow, @add_pow]

  have prev1: f (∑ m in Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(Nat.choose n m)) ≤  ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) :=by{

    -- triangle inequality
    have l1: f (∑ m in Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(Nat.choose n m)) ≤ ∑ m in Finset.range (n + 1), f (x ^ m * y ^ (n - m) * ↑(Nat.choose n m)):= by{
      have : IsAbsoluteValue f.toFun :=by{exact my_f_is_absval }
      --apply abv_sum_le_sum_abv (fun k => x ^ k * y ^ (n - k) * ↑(Nat.choose n k)) (Finset.range (n + 1))
      apply IsAbsoluteValue.abv_sum f.toFun (fun i => x ^ i * y ^ (n - i) * ↑(Nat.choose n i)) (Finset.range (n + 1))

      }

    --norm is multiplicative
    have l2: ∑ i in Finset.range (n + 1), f ( x^i * y^(n - i) * (n.choose i) )
      = ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) * f (n.choose i) :=by{
        congr
        ext
        rw[f.map_mul', f.map_mul']
      }
    rw[l2] at l1
    -- hf
    have l3:  ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) * f (n.choose i)
      ≤  ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) :=by{
        apply Finset.sum_le_sum
        intros i hi
        conv => rhs
                rw[ ←mul_one (f (x ^ i) * f (y ^ (n - i)))]
        exact mul_le_mul_of_nonneg_left (hf _) (mul_nonneg (map_nonneg f _) (map_nonneg f _))
      }
    linarith
  }

    -- We use my_ineq1
  have prev2:  ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) ≤ (n + 1 : ℝ) * (max (f x) (f y) )^n :=by{
    have l1: ∑ i in Finset.range (n + 1), f (x ^ i) * f (y ^ (n - i)) ≤ ∑ i in Finset.range (n + 1), (max (f x) (f y) )^n:= by{
      apply Finset.sum_le_sum
      intros i hi
      have : i + (n - i) = n := by{
        rw [Nat.add_comm]
        apply Nat.sub_add_cancel
        simp at hi
        linarith
       }
      conv => rhs
              rw[←this]
      simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_pow, ge_iff_le, Nat.cast_add]
      rw[←Real.rpow_nat_cast, ←Real.rpow_nat_cast ]
      exact my_ineq1  i (n-i) (map_nonneg f.toMulRingSeminorm x) (map_nonneg f.toMulRingSeminorm y)

    }
    have l2: ∑ i in Finset.range (n + 1), (max (f x) (f y) )^n = (n + 1 : ℝ) * max (f x) (f y) ^ n :=by{
      simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, ge_iff_le, Real.rpow_nat_cast,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      }
    linarith
  }
  norm_num at prev1
  norm_num at prev2
  linarith
  done


lemma my_max_ineq {n : ℕ} (x y : ℚ) (hn : n ≠ 0) (hf : ∀ m : ℕ, f m ≤ 1) :
  f (x + y) ≤ (n + 1 : ℝ) ^ (1 / (n : ℝ)) * max (f x) (f y) := by
  refine le_of_pow_le_pow n ?hb (Nat.pos_of_ne_zero hn)  ?h
  · apply mul_nonneg
    · apply Real.rpow_nonneg_of_nonneg
      norm_cast
      exact Nat.zero_le (n + 1)
    · norm_num
  · simp only [ Real.rpow_nat_cast, mul_pow]
    have : 0 ≤ (n : ℝ) + 1 := by {
      norm_cast
      linarith }
    conv => rhs
            rw[←Real.rpow_nat_cast, ←Real.rpow_mul this (1 / ↑n) n , one_div]
    rw[inv_mul_cancel ]
    · simp only [Real.rpow_one]
      rw[← Real.rpow_nat_cast,← Real.rpow_nat_cast]
      exact my_max_ineq' n x y hf
    · exact Nat.cast_ne_zero.mpr hn

  done

/-This is the auxiliar limit we need for the proof-/


lemma my_limit_aux: Filter.Tendsto (λ x : ℕ => ( (x : ℝ)+1)^(1 / (x : ℝ))) Filter.atTop (nhds 1) :=by
  have: (λ x : ℕ => ( (x : ℝ)+1)^(1 / (x : ℝ)))= (λ x : ℕ => (1+ 1*(x : ℝ))^(1 / (x : ℝ))):=by{
    rw [@Function.funext_iff]
    intro n
    rw [@add_comm]
    simp only [one_div, one_mul]
  }
  rw[this]
  simp only [one_div]
  exact my_limit2  zero_lt_one
  done

/- Result for step 2.1 in the outline -/

lemma my_nonarch_iff_bound:  my_nonarchimedean f  ↔ (∀ n: ℕ, f n ≤ 1) := by
  constructor
  · exact fun a n => my_bounded_N a n
  simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe]
  unfold my_nonarchimedean
  intros all r s
  have lim :  Filter.Tendsto (λ n : ℕ => (n + 1 : ℝ) ^ (1 / (n : ℝ)) * max (f r) (f s)) Filter.atTop (nhds (max (f r) (f s))):=by{
    rw[←one_mul (max (f r) (f s)) ]

    apply Filter.Tendsto.mul
    · exact my_limit_aux
    · rw[one_mul (max (f r) (f s)) ]
      exact tendsto_const_nhds

  }
  apply  ge_of_tendsto lim _
  simp only[Filter.eventually_atTop, ge_iff_le ]
  use 1
  intros b hb
  have nb : b ≠ 0 := by{ exact Nat.one_le_iff_ne_zero.mp hb }
  exact my_max_ineq r s nb all

  done
/- We deduce trivially step 2.2 in the outline-/


lemma my_arch_iff_unbound {g : MulRingNorm ℚ }:  ¬ my_nonarchimedean g  ↔ (∃ n: ℕ, 1 < g n ) := by
  rw [@not_iff_comm, my_nonarch_iff_bound, @not_exists]
  simp [not_lt]

  done

/- To formalise step 2.3 we need to use  Nat.find and Nat.find_spec that allow us to find the natural number satisfying a certain property. -/

lemma my_n0  (le : ∃ n : ℕ, 1 < f n) (hn : n0 = Nat.find le) : 1 < n0 := by
rw [hn, @Nat.one_lt_iff_ne_zero_and_ne_one]
have th := Nat.find_spec le --We should explain this
constructor
· by_contra z
  rw[z] at th
  simp [f.map_zero'] at th
  linarith

· by_contra z
  rw[z] at th
  simp [f.map_one'] at th

done

/-Lemmas for steps 2.4a and 2.4b-/




lemma my_fn0_eq_n0a (le : ∃ n : ℕ, 1 < f n) (hn : n0 = Nat.find le)  (ha: a= Real.log (f n0) / Real.log n0 ): f n0 = n0^a :=by
  have: 2 ≤ n0:=by exact my_n0 le hn
  have hn' := Nat.find_spec le
  rw[ha, Real.log_div_log]
  apply Eq.symm
  apply Real.rpow_logb
  · norm_cast
    linarith
  · norm_cast
    linarith
  · rw[hn]
    linarith -- it uses hn'
  done

lemma my_0_lt_a (le : ∃ n : ℕ, 1 < f n) (hn : n0 = Nat.find le)  (ha: a= Real.log (f n0) / Real.log n0 ): 0 < a :=by
  have ineq : (1:ℝ )<n0 := by {
  norm_cast
  exact my_n0 le hn}
  nth_rewrite 1 [hn] at ha
  rw[ha]
  apply div_pos
  · exact Real.log_pos (Nat.find_spec le)
  · exact log_pos ineq
  done

-- In order to prove the statement we are going to use the following
#eval  Nat.digits 3 19 -- this gives us a list based on the decomposition 19= 1*3^0+ 0*3^1+ 2*3^1
#eval  (Nat.digits 3 19).length
#check  (Nat.digits 3 19).nthLe



-- This lemma is a missing step for the next proof
lemma my_eq'{m n :ℕ }(hm: 1 < m)(hn: 1 < n): (m: ℚ )=  (∑ i in Finset.range ((Nat.digits n m).length), (List.getI (Nat.digits n m) i) * ((n ^ i): ℚ ) ):=by

sorry




lemma my_prev1_nice_bound (m n :ℕ )(le : ∃ n : ℕ, 1 < f n)(hm: 1 < m)(hn: 1 < n) : f m ≤ (1+ log m / log n)* n *(f n)^( log m / log n) := by

  let r : ℕ := (Nat.digits n m).length
  have rr: r =(Nat.digits n m).length  := by{rfl}

  have helpm: (0:ℝ )< m:=by{
    norm_cast
    exact Nat.zero_lt_of_lt hm}

  have helpn: (0:ℝ )< n:=by{
    norm_cast
    exact Nat.zero_lt_of_lt hn}

  have helpnr: (0:ℝ )< n^r:=by{
    refine rpow_pos_of_pos ?hx ↑r
    norm_cast
    exact Nat.zero_lt_of_lt hn
    }
  -- I have this proved, but there was a missunderstanding with the indexing and I had to change it...
  have inr' : r≤ 1+ log m / log n := by{
    have aux : r= 1+ (Nat.log n m) := by{
    rw[rr]
    sorry
    }
    rw[aux]
    simp only [Nat.cast_add, Nat.cast_one, add_le_add_iff_left]
    have aux' : log m / log n = (Real.logb n m) := by{exact rfl}
    rw[aux']
    sorry
  }

  have g0: 0 < log m/log n:= by{
    refine div_pos_iff.mpr ?_
    apply Or.intro_left
    apply And.intro
    · refine (log_pos_iff helpm).mpr ?h.left.a
      norm_cast
    · refine log_pos ?h.right.hx
      norm_cast
   }

  have l1: f m ≤ ∑ i in Finset.range ((Nat.digits n m).length), (f ((Nat.digits n m).getI i )) *(f n)^(i: ℕ ) :=by{

    have l10: f m ≤ ∑ i in  Finset.range ((Nat.digits n m).length), f ( ((Nat.digits n m).getI i )* (( n^(i: ℕ ) ):ℚ )) :=by{

    have ins: IsAbsoluteValue f.toFun :=by{exact my_f_is_absval }

    have : f
      (∑ i in Finset.range ((Nat.digits n m).length), (List.getI (Nat.digits n m) i) * ((n ^ i): ℚ ) ) ≤
    ∑ i in Finset.range ((Nat.digits n m).length),
      AddGroupSeminorm.toFun f.toAddGroupSeminorm ((List.getI (Nat.digits n m) i) * ((n ^ i): ℚ ) ):=by{
        refine IsAbsoluteValue.abv_sum f.toFun  (fun i  => ((List.getI (Nat.digits n m) i))*((n ^ i): ℚ ) ) (Finset.range ((Nat.digits n m).length ))

      }

    suffices ob: (m: ℚ )=  (∑ i in Finset.range ((Nat.digits n m).length), (List.getI (Nat.digits n m) i) * ((n ^ i): ℚ ) )
    {rw[ob]
     exact this
      }

    exact my_eq' hm hn

    }

    suffices ob1: ∑ i in Finset.range ((Nat.digits n m).length),
      f ((List.getI (Nat.digits n m) i) * ((n ^ i): ℚ ) ) = ∑ i in Finset.range ((Nat.digits n m).length), (f ((Nat.digits n m).getI i )) *(f n)^(i: ℕ )
    {rw[← ob1]
     exact l10
    }
    simp only [ne_eq, Nat.cast_pow, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, map_mul, map_pow,
      Real.rpow_nat_cast]

    }

  have l2:∑ i in Finset.range ((Nat.digits n m).length), (f ((Nat.digits n m).getI i )) *(f n)^(i: ℕ )  ≤ (r )* n * (f n)^(r-1) := by calc

    ∑ i in Finset.range ((Nat.digits n m).length), (f ((Nat.digits n m).getI i )) *(f n)^(i: ℕ )  ≤ ∑ i in Finset.range ((Nat.digits n m).length), (f ((Nat.digits n m).getI i ))* (f n)^(r-1) := by{
      refine Finset.sum_le_sum ?h30

      intros i ir
      refine mul_le_mul_of_nonneg_left ?b110 my_f_nneg
      have pup1: i ≤ (r-1 : ℝ ):=by{
        rw[← rr] at ir
        sorry}

      exact Real.rpow_le_rpow_of_exponent_le (my_f_ge1 le hn) (pup1 )


     }

    _ ≤ ∑ i in Finset.range ((Nat.digits n m).length), n * (f n)^(r-1) := by{
      rw[← rr]
      rw [← @Finset.sum_mul, ← @Finset.sum_mul]

      have : (∑ x in Finset.range r, AddGroupSeminorm.toFun f.toAddGroupSeminorm ↑(List.getI (Nat.digits n m) x)) ≤ (∑ x in Finset.range r, ↑n):=by{
      refine Finset.sum_le_sum ?h300
      intros i ir
      sorry}

      refine mul_le_mul_of_nonneg_right this ?a110
      refine rpow_nonneg_of_nonneg (my_f_nneg) (r - 1 : ℝ )

      }
    _ = ( r)* n * (f n)^(r-1) := by{
      rw[← rr]

      have: ∑ i in Finset.range (r), (n: ℝ ) = ( r)* (n ) := by{
        simp only [ne_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_eq_mul_right_iff, self_eq_add_left,
          one_ne_zero, Nat.cast_eq_zero, false_or]
      }
      rw[← this]
      rw [@Finset.sum_mul]
      }

  have l3: (r)* n * (f n)^(r-1) ≤ (1+ log m / log n)* n *(f n)^( log m / log n) := by calc
      (r)* n * (f n)^(r-1) ≤ (1+ log m / log n)* n *(f n)^(r-1) := by{

        rw [@mul_assoc, @mul_assoc]
        have : 0 < n * (f n )^(r -1 :ℝ ) :=by{
          rw [@mul_pos_iff]
          apply Or.intro_left
          apply And.intro
          · norm_cast
            exact Nat.zero_lt_of_lt hn
          · apply rpow_pos_of_pos ?_ (↑r-1)
            have: 0≠ (n:ℚ ):=by{
              norm_cast
              linarith
            }
            exact my_f_pos this

        }
        suffices logic: (r) ≤ (1+ log m / log n)
        { exact (mul_le_mul_right this).mpr logic }
        exact inr'


        }
      _ ≤ (1+ log m / log n)* n *(f n)^( log m / log n) := by{
        have : 0 <(1+ log m / log n)* n  :=by{
            rw [@mul_pos_iff]
            apply Or.intro_left
            apply And.intro
            · refine add_pos ?h.left.ha g0
              exact Real.zero_lt_one
            · norm_cast
              exact Nat.zero_lt_of_lt hn
          }
        suffices pr: f n^(r-1) ≤ f n ^ (log ↑m / log ↑n)
        {
          refine (mul_le_mul_left this).mpr pr
          }

        refine rpow_le_rpow_of_exponent_le ?nr ?inr'
        exact my_f_ge1 le hn
        exact tsub_le_iff_left.mpr inr'

        }

  linarith
  done

lemma my_nice_bound (m n :ℕ )(le : ∃ n : ℕ, 1 < f n)(hm: 1 < m)(hn: 1 < n): f m ≤ (f n) ^( log m / log n):= by
  let r : ℕ := (Nat.digits n m).length
  have rr: r =(Nat.digits n m).length  := by{rfl}

  have helpm: (0:ℝ )< m:=by{
    norm_cast
    exact Nat.zero_lt_of_lt hm}

  have helpn: (0:ℝ )< n:=by{
    norm_cast
    exact Nat.zero_lt_of_lt hn}

  have g0: 0 < log m/log n:= by{
    refine div_pos_iff.mpr ?_
    apply Or.intro_left
    apply And.intro
    · refine (log_pos_iff helpm).mpr ?h.left.a
      norm_cast
    · refine log_pos ?h.right.hx
      norm_cast
   }


  have prev1{s:ℕ }(hs': 1 < s): f s ≤ (1+ log s / log n)* n *(f n)^( log s / log n):=by{
    exact my_prev1_nice_bound s n le hs' hn
    }

  have prev2 {t: ℕ }(ht:  0< t): f m ≤ (1+ (log m / log n) *t )^(1/t)* n^(1/t) *(f n)^( log m / log n) :=by{
    intros
    have ht': (0: ℝ )≤ 1/t:=by{ simp only [one_div, inv_nonneg, Nat.cast_nonneg]}

    have one: f m = (f (m^ t))^(1/ (t:ℝ )):=by{
      have again: t ≠ 0 :=by{linarith}
      simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Nat.cast_pow, map_pow, one_div]
      have: 0 ≤ f m:=by{exact my_f_nneg}
      simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe] at this
      conv_lhs => rw[← pow_nat_rpow_nat_inv  this again]
    }

    have two: f ↑n ^ (log ↑m / log ↑n) = (f ↑n ^ (log ((m^t):ℝ ) / log ↑n))^(1/(t:ℝ )):=by {
      simp only [Real.rpow_nat_cast, log_pow, one_div]
      have: 0 ≤ f n:=by{exact my_f_nneg}
      conv_rhs => rw[← rpow_mul this (↑t * log ↑m / log ↑n)  ((↑t)⁻¹)]
      rw[@division_def, @division_def, ← mul_rotate, ← mul_assoc, mul_assoc, ← mul_rotate, mul_assoc]
      simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, ne_eq, Nat.cast_eq_zero]
      have nw (ht:  0< t): (t:ℝ )⁻¹ * (t:ℝ )=1 :=by{
          refine inv_mul_cancel ?h_1
          refine Nat.cast_ne_zero.mpr ?h.a
          linarith
       }
      rw[nw ht, mul_one]

    }
    have three: (1 + log ↑m / log ↑n * ↑t) ^ (1 / ↑t) * ↑n ^ (1 / ↑t) *(f ↑n ^ (log ((m ^ t):ℝ ) / log ↑n)) ^ (1 / ↑t)=((1 + log (((m ^ t:ℕ )):ℝ ) / log ↑n ) * ↑n *(f ↑n ^ (log (((m ^ t:ℕ )):ℝ ) / log ↑n)) )^ (1 / ↑t):=by {
      simp only [one_div, AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, Real.rpow_nat_cast, log_pow,
        Nat.cast_pow]
      conv_rhs => rw[mul_rotate, mul_assoc]
      rw[Real.mul_rpow]
      · rw[Real.mul_rpow]
        · conv_rhs => rw[← mul_assoc, ← mul_rotate]
          have obv: ↑t * log ↑m / log ↑n= log ↑m / log ↑n * ↑t :=by{
            rw[@division_def,@division_def, mul_rotate]
          }
          rw[obv]
        · sorry --refine Real.rpow_nonneg_of_nonneg ?h.hx (↑t * log ↑m / log ↑n)

          --· exact my_f_nonneg
        · sorry
      · norm_cast
        linarith
      · sorry
    -- Enough inequalities at this point (Lean also gets tired of checking)
    }
    conv_lhs => rw[one]
    conv_rhs => rw[two, three]

    refine rpow_le_rpow ?h6 ?prev1 ht'
    · exact my_f_nneg
    · have : 1< m^t:= by{sorry}
      exact prev1 this


  }

  have lim :  Filter.Tendsto (λ t : ℕ => (1+ (log m / log n) *t )^(1/t)* n^(1/t) *(f n)^( log m / log n) ) Filter.atTop (nhds ((f n)^( log m / log n))):=by{

    have red1: Filter.Tendsto (λ t : ℕ => (1+ (log m / log n) *t )^(1/t)* n^(1/t) ) Filter.atTop (nhds (1)):=by{
      nth_rewrite 4 [(one_mul 1).symm]
      simp only [one_div]
      apply Filter.Tendsto.mul
      · exact my_limit2 g0
      · exact my_limit1 helpn
      }
    nth_rewrite 2 [(one_mul ((f n)^( log m / log n))).symm]
    exact Tendsto.mul_const (AddGroupSeminorm.toFun f.toAddGroupSeminorm ↑n ^ (log ↑m / log ↑n)) red1
    }

  apply  ge_of_tendsto lim _
  simp only[Filter.eventually_atTop, ge_iff_le ]
  use 1
  intros b hb
  have nb : 0 < b := by{ exact hb}
  exact prev2 nb
  done

--


lemma my_nice_eq {m n :ℕ }(hm: 1 < m)(hn: 1 < n)(le : ∃ n : ℕ, 1 < f n): (f m) = (f n) ^(log m/ log n):=by
  refine le_antisymm_iff.mpr ?_
  have ltn: 0< log (n:ℝ) := by{
    refine log_pos ?hx'
    exact Nat.one_lt_cast.mpr hn
    }
  have ltm: 0< log (m:ℝ) := by{
    refine log_pos ?hx''
    exact Nat.one_lt_cast.mpr hm
    }
  apply And.intro
  · exact my_nice_bound m n le hm hn
  · suffices: f n ≤ (f m) ^(log n/ log m)
    { have eq: f m = (f m^(log n/ log m) )^(log m/ log n) :=by{
      rw [@division_def,@division_def]
      rw[←Real.rpow_mul ]
      · rw [← @mul_assoc]
        have no:  (log ↑m)⁻¹ * log ↑m=1 := by{
          rw [@inv_mul_eq_div]
          refine div_self ?h
          exact ne_of_gt ltm
          }
        have ni:  (log ↑n)⁻¹ * log ↑n=1 := by{
          rw [@inv_mul_eq_div]
          refine div_self ?h'
          exact ne_of_gt ltn
          }
        rw [← @mul_rotate,← @mul_assoc,@mul_assoc ]
        rw [no, ni]
        simp only [ mul_one, Real.rpow_one]
      · exact map_nonneg f.toMulRingSeminorm (m:ℚ )
      }
      rw[eq]
      refine rpow_le_rpow ?right.h this ?right.h₂
      · exact map_nonneg f.toMulRingSeminorm (n:ℚ )
      · rw [@div_nonneg_iff]
        apply Or.intro_left
        apply And.intro
        · exact log_nat_cast_nonneg m
        · exact log_nat_cast_nonneg n

     }
    exact my_nice_bound n m le hn hm
  done

lemma my_nicer_eq {m n :ℕ }(hm: 1 < m)(hn: 1 < n)(le : ∃ n : ℕ, 1 < f n): (f m)^(1/log m) = (f n) ^(1/ log n):=by
  suffices nice: (f m) = (f n) ^(log m/ log n)
  { rw [@division_def, nice, ←Real.rpow_mul, @division_def,← @mul_assoc, ← @mul_rotate,← @mul_assoc]
    have ltm: 0< log (m:ℝ) := by{
    refine log_pos ?hx''
    exact Nat.one_lt_cast.mpr hm
    }
    have no:  (log ↑m)⁻¹ * log ↑m=1 := by{
          rw [@inv_mul_eq_div]
          refine div_self ?h
          exact ne_of_gt ltm
          }
    rw[no]
    simp only [ mul_one, Real.rpow_one]
    rw[@division_def]
    exact my_f_nneg
    }
  exact my_nice_eq hm hn le
  done



lemma my_almost_there {n: ℕ} (hm: 1< n) (le : ∃ n : ℕ, 1 < f n) (hn : n0 = Nat.find le)  (ha: a= Real.log (f n0) / Real.log n0 ): f n = n^a :=by
  have l1 {n:ℕ} (h': 1 <n): 0< f n :=by{
    have ne: 0≠ (n:ℚ) :=by{
      norm_cast
      linarith
    }
    exact my_f_pos ne
  }
  have step2: f n = (f n0 ^(1/log n0))^log n :=by{

    have step: f n ^(1/ log n)= f n0 ^(1/log n0):=by{exact  my_nicer_eq hm (my_n0 le hn) le}
    rw [← step]
    rw[← Real.rpow_mul]
    simp only [AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe, one_div, ne_eq, log_eq_zero, Nat.cast_eq_zero,
      Nat.cast_eq_one]
    have ltn: 0< log (n:ℝ) := by{
      refine log_pos ?hx'
      exact Nat.one_lt_cast.mpr hm
      }
    have ni:  (log ↑n)⁻¹ * log ↑n=1 := by{
      rw [@inv_mul_eq_div]
      refine div_self ?h'
      exact ne_of_gt ltn
      }
    rw[ni]
    simp only [Real.rpow_one]
    exact my_f_nneg
  }

  have step3:  log (f n) = log (n)*( log (f n0) /log n0):= by{
    rw[step2]
    rw[← Real.rpow_mul]
    have: 0< f n0:=by{ exact l1 (my_n0 le hn) }

    rw [← Real.rpow_eq_pow]
    conv => lhs
            apply Real.log_rpow this (1 / log ↑n0 * log ↑n)
    · rw [@mul_rotate, @mul_assoc, @mul_one_div]
    · exact my_f_nneg
    }

  have step4: f n = n^( log (f n0) /log n0) :=by{
    rw [← @exp_eq_exp] at step3
    conv_lhs =>  rw[← Real.exp_log (l1 hm), step3]
    have: (0: ℝ )< ↑n:=by{
      norm_num
      linarith
    }
    have l2{n:ℕ} (h': 1 <n): 0< ↑n ^ (log (AddGroupSeminorm.toFun f.toAddGroupSeminorm ↑n0) / log ↑n0) :=by{
      rw[← ha]
      apply rpow_pos_of_pos ?_ a
      norm_num
      linarith
    }
    conv_rhs =>  rw[← Real.exp_log (l2 hm)]
    simp only [exp_eq_exp]
    rw[← ha] --this is just to see things clearly
    conv_rhs => rw[Real.log_rpow this a, mul_comm]
    }
  rw [ha]
  exact step4
  done


lemma my_is_there (le : ∃ n : ℕ, 1 < f n) (hn : n0 = Nat.find le)  (ha: a= Real.log (f n0) / Real.log n0 ): ∀ n : ℕ , f n = n^a :=by
  intro n
  cases n with
  | zero => have na: 0≠ a:=by{
              rw [ha]
              rw [@ne_iff_lt_or_gt]
              apply Or.intro_left
              exact my_0_lt_a le hn rfl
            }

            simp only [Nat.zero_eq, CharP.cast_eq_zero, AddGroupSeminorm.toFun_eq_coe, map_zero, ne_eq]
            exact (Real.zero_rpow (id (Ne.symm na))).symm

  | succ n => cases n with
    | zero => simp only [Nat.zero_eq, Nat.cast_one, AddGroupSeminorm.toFun_eq_coe,
      MulRingSeminorm.toFun_eq_coe, map_one, Real.one_rpow]
    | succ n => have puff {n: ℕ }: Nat.succ (Nat.succ n)= n+1+1:= by{rfl}
                rw [puff]
                have uf: 1 < ↑(n + 1 + 1):=by{
                  simp only [Nat.cast_add, Nat.cast_one, lt_add_iff_pos_left]
                  exact Nat.cast_add_one_pos n
                 }
                exact my_almost_there uf le hn ha

  done



--lemma my_nat_ext  (f g : MulRingNorm ℚ) (h : ∀n:ℕ, f n = g n) : f=g
lemma my_cast_f {c: Real } (g': MulRingNorm ℚ )(g: MulRingNorm ℚ ) (h0 : ∀ (n:ℕ ), g n = (g' n)^c):∀ q:ℚ, g q = (g' q)^c := by

  -- analogous to other lemma
  sorry


lemma my_then_real (h: ¬ my_nonarchimedean f) : my_equiv my_abs_real f:= by
  rw[my_arch_iff_unbound ] at h
  let n0: ℕ := Nat.find h
  have hn0 : n0= Nat.find h := by rfl
  let a: ℝ:= Real.log (f n0) / Real.log n0
  have ha: a= Real.log (f n0) / Real.log n0 := by rfl

  have L0 (n: ℕ ): f n = my_abs_real.toFun (Nat.cast n)^a := by{
    have l1 (n: ℕ): f n = n^a := by{
    exact my_is_there h hn0 ha n }

    have l2 {n:ℕ}: my_abs_real (Nat.cast n) = Nat.cast n := by{
      unfold my_abs_real
      simp only
      rw [← Rat.norm_cast_real]
      simp only [Rat.cast_coe_nat, IsROrC.norm_natCast]
      }
    rw[l1, l2]
    }
  unfold my_equiv
  use a
  constructor
  rw[ha]
  have b1: Real.log ↑n0 > 0 := by{
    have bd1 : (1:ℝ)  < n0 := by {
      refine Nat.one_lt_cast.mpr ?_
      exact my_n0 h hn0}
    exact Real.log_pos bd1
    }
  have b2:  Real.log (AddGroupSeminorm.toFun f.toAddGroupSeminorm ↑n0)> 0 := by{
    have bd2: 1 < AddGroupSeminorm.toFun f.toAddGroupSeminorm ↑n0 := by{
      apply Nat.find_spec h}
    exact Real.log_pos bd2
    }
  exact div_pos b2 b1

  exact fun x => (my_cast_f my_abs_real f L0 x).symm
