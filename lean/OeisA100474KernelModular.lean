import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic

/-!
Kernel-checkable modular-exponentiation certificates for OEIS A100474.

The concrete arithmetic is normalized by `norm_num` into proof terms.  No
native code evaluator or `Lean.trustCompiler` is used.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.KernelModular

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bs => 2 * bitsValue bs + b.toNat

def natPowModBits (base modulus : Nat) : List Bool → Nat
  | [] => 1 % modulus
  | b :: bs =>
      let r := natPowModBits base modulus bs
      let r2 := r * r % modulus
      if b then r2 * base % modulus else r2

def zmodPowBits {p : Nat} (base : ZMod p) : List Bool → ZMod p
  | [] => 1
  | b :: bs =>
      let r := zmodPowBits base bs
      if b then r * r * base else r * r

theorem zmodPowBits_eq_pow {p : Nat} (base : ZMod p) (bits : List Bool) :
    zmodPowBits base bits = base ^ bitsValue bits := by
  induction bits with
  | nil => simp [zmodPowBits, bitsValue]
  | cons b bs ih =>
      cases b <;> simp [zmodPowBits, bitsValue, ih, two_mul, pow_add]

theorem natPowModBits_cast (base modulus : Nat) (bits : List Bool) :
    (natPowModBits base modulus bits : ZMod modulus) =
      zmodPowBits (base : ZMod modulus) bits := by
  induction bits with
  | nil => simp [natPowModBits, zmodPowBits, ZMod.natCast_mod]
  | cons b bs ih =>
      cases b
      · simp only [natPowModBits, Bool.false_eq_true, ↓reduceIte, zmodPowBits]
        rw [ZMod.natCast_mod, Nat.cast_mul, ih]
      · simp only [natPowModBits, ↓reduceIte, zmodPowBits]
        rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul, ih]

theorem zmod_pow_eq_of_natPowModBits
    (base modulus exponent result : Nat) (bits : List Bool)
    (hbits : bitsValue bits = exponent)
    (hcalc : natPowModBits base modulus bits = result) :
    (base : ZMod modulus) ^ exponent = (result : ZMod modulus) := by
  rw [← hbits, ← zmodPowBits_eq_pow]
  rw [← natPowModBits_cast, hcalc]

theorem zmod_natCast_ne_one (result modulus : Nat)
    (hresult : result < modulus) (hmodulus : 1 < modulus)
    (hne : result ≠ 1) : (result : ZMod modulus) ≠ 1 := by
  intro h
  have hc : (result : ZMod modulus) = ((1 : Nat) : ZMod modulus) := by
    simpa using h
  have h' : result % modulus = 1 % modulus :=
    (ZMod.natCast_eq_natCast_iff' result 1 modulus).mp hc
  rw [Nat.mod_eq_of_lt hresult, Nat.mod_eq_of_lt hmodulus] at h'
  exact hne h'

/- Lucas certificate 0: modulus 73098925036309721. -/
def bits_0_0 : List Bool := [false, false, false, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, true]

theorem modpow_0_0 : (3 : ZMod 73098925036309721) ^ 73098925036309720 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 3 73098925036309721 73098925036309720 1 bits_0_0
  · norm_num [bits_0_0, bitsValue]
  · norm_num [bits_0_0, natPowModBits]

def bits_0_1 : List Bool := [false, false, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, true]

theorem modpow_0_1 : (3 : ZMod 73098925036309721) ^ 36549462518154860 = 73098925036309720 := by
  apply zmod_pow_eq_of_natPowModBits 3 73098925036309721 36549462518154860 73098925036309720 bits_0_1
  · norm_num [bits_0_1, bitsValue]
  · norm_num [bits_0_1, natPowModBits]

def bits_0_2 : List Bool := [false, false, false, true, true, true, true, true, false, false, false, true, false, true, true, true, false, false, true, true, false, false, false, false, false, false, true, false, true, true, true, true, true, false, true, true, true, false, false, true, false, false, false, false, true, true, true, true, true, true, false, false, true, true]

theorem modpow_0_2 : (3 : ZMod 73098925036309721) ^ 14619785007261944 = 37653479805228602 := by
  apply zmod_pow_eq_of_natPowModBits 3 73098925036309721 14619785007261944 37653479805228602 bits_0_2
  · norm_num [bits_0_2, bitsValue]
  · norm_num [bits_0_2, natPowModBits]

def bits_0_3 : List Bool := [false, false, false, true, true, false, false, false, true, true, false, false, true, false, false, true, false, false, true, true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, true, false, true, false, true, true, false, false, true]

theorem modpow_0_3 : (3 : ZMod 73098925036309721) ^ 21293016322840 = 40677704959439497 := by
  apply zmod_pow_eq_of_natPowModBits 3 73098925036309721 21293016322840 40677704959439497 bits_0_3
  · norm_num [bits_0_3, bitsValue]
  · norm_num [bits_0_3, natPowModBits]

def bits_0_4 : List Bool := [false, false, false, true, true, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false, false, true, false, true, false, true, true, true, true, true, true, true, true, false, false, true, true, false, false, true, true, true, true]

theorem modpow_0_4 : (3 : ZMod 73098925036309721) ^ 16715967307640 = 2726861515707806 := by
  apply zmod_pow_eq_of_natPowModBits 3 73098925036309721 16715967307640 2726861515707806 bits_0_4
  · norm_num [bits_0_4, bitsValue]
  · norm_num [bits_0_4, natPowModBits]

def bits_0_5 : List Bool := [false, false, false, true, true, false, true, false, true, true, true, true, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, false, true, true, true, false, true, false, false, true, false, true, false, false, true, true]

theorem modpow_0_5 : (3 : ZMod 73098925036309721) ^ 6953193668440 = 9985547038106212 := by
  apply zmod_pow_eq_of_natPowModBits 3 73098925036309721 6953193668440 9985547038106212 bits_0_5
  · norm_num [bits_0_5, bitsValue]
  · norm_num [bits_0_5, natPowModBits]

def bits_0_6 : List Bool := [false, false, false, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, false, true, true, false, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, false, true, true, false, true]

theorem modpow_0_6 : (3 : ZMod 73098925036309721) ^ 6313060284680 = 5706157203313533 := by
  apply zmod_pow_eq_of_natPowModBits 3 73098925036309721 6313060284680 5706157203313533 bits_0_6
  · norm_num [bits_0_6, bitsValue]
  · norm_num [bits_0_6, natPowModBits]

theorem lucas_hcheck_0 :
    ((3 : ZMod 73098925036309721) ^ (73098925036309721 - 1) = 1 ∧
      [2, 2, 2, 5, 3433, 4373, 10513, 11579].Forall
        (fun q => (3 : ZMod 73098925036309721) ^ ((73098925036309721 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_0_0
  · simp only [List.forall_cons]
    have h1 : (73098925036309720 : ZMod 73098925036309721) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (37653479805228602 : ZMod 73098925036309721) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (40677704959439497 : ZMod 73098925036309721) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (2726861515707806 : ZMod 73098925036309721) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h5 : (9985547038106212 : ZMod 73098925036309721) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h6 : (5706157203313533 : ZMod 73098925036309721) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_0_1, modpow_0_2, modpow_0_3, modpow_0_4, modpow_0_5, modpow_0_6,
      h1, h2, h3, h4, h5, h6]

/- Lucas certificate 1: modulus 584791400290477769. -/
def bits_1_0 : List Bool := [false, false, false, true, false, false, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, true]

theorem modpow_1_0 : (3 : ZMod 584791400290477769) ^ 584791400290477768 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 3 584791400290477769 584791400290477768 1 bits_1_0
  · norm_num [bits_1_0, bitsValue]
  · norm_num [bits_1_0, natPowModBits]

def bits_1_1 : List Bool := [false, false, true, false, false, true, true, false, true, true, false, false, true, true, false, false, false, true, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, true]

theorem modpow_1_1 : (3 : ZMod 584791400290477769) ^ 292395700145238884 = 584791400290477768 := by
  apply zmod_pow_eq_of_natPowModBits 3 584791400290477769 292395700145238884 584791400290477768 bits_1_1
  · norm_num [bits_1_1, bitsValue]
  · norm_num [bits_1_1, natPowModBits]

def bits_1_2 : List Bool := [false, false, false, true]

theorem modpow_1_2 : (3 : ZMod 584791400290477769) ^ 8 = 6561 := by
  apply zmod_pow_eq_of_natPowModBits 3 584791400290477769 8 6561 bits_1_2
  · norm_num [bits_1_2, bitsValue]
  · norm_num [bits_1_2, natPowModBits]

theorem lucas_hcheck_1 :
    ((3 : ZMod 584791400290477769) ^ (584791400290477769 - 1) = 1 ∧
      [2, 2, 2, 73098925036309721].Forall
        (fun q => (3 : ZMod 584791400290477769) ^ ((584791400290477769 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_1_0
  · simp only [List.forall_cons]
    have h1 : (584791400290477768 : ZMod 584791400290477769) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (6561 : ZMod 584791400290477769) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_1_1,
      h1, h2]

/- Lucas certificate 2: modulus 1190470901. -/
def bits_2_0 : List Bool := [false, false, true, false, true, true, true, true, false, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, true, false, false, false, true]

theorem modpow_2_0 : (2 : ZMod 1190470901) ^ 1190470900 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 2 1190470901 1190470900 1 bits_2_0
  · norm_num [bits_2_0, bitsValue]
  · norm_num [bits_2_0, natPowModBits]

def bits_2_1 : List Bool := [false, true, false, true, true, true, true, false, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, true, false, false, false, true]

theorem modpow_2_1 : (2 : ZMod 1190470901) ^ 595235450 = 1190470900 := by
  apply zmod_pow_eq_of_natPowModBits 2 1190470901 595235450 1190470900 bits_2_1
  · norm_num [bits_2_1, bitsValue]
  · norm_num [bits_2_1, natPowModBits]

def bits_2_2 : List Bool := [false, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, true, false, false, false, true, true, false, false, false, true, true, true]

theorem modpow_2_2 : (2 : ZMod 1190470901) ^ 238094180 = 1024009807 := by
  apply zmod_pow_eq_of_natPowModBits 2 1190470901 238094180 1024009807 bits_2_2
  · norm_num [bits_2_2, bitsValue]
  · norm_num [bits_2_2, natPowModBits]

def bits_2_3 : List Bool := [false, false, true, false, true, true, false, true, true, false, false, true, false, false, false, true, false, false, true, true, false, true, false, false, false, false, true]

theorem modpow_2_3 : (2 : ZMod 1190470901) ^ 70027700 = 520341107 := by
  apply zmod_pow_eq_of_natPowModBits 2 1190470901 70027700 520341107 bits_2_3
  · norm_num [bits_2_3, bitsValue]
  · norm_num [bits_2_3, natPowModBits]

def bits_2_4 : List Bool := [false, false, true, false, false, true, false, true, false, true, true]

theorem modpow_2_4 : (2 : ZMod 1190470901) ^ 1700 = 1027742841 := by
  apply zmod_pow_eq_of_natPowModBits 2 1190470901 1700 1027742841 bits_2_4
  · norm_num [bits_2_4, bitsValue]
  · norm_num [bits_2_4, natPowModBits]

theorem lucas_hcheck_2 :
    ((2 : ZMod 1190470901) ^ (1190470901 - 1) = 1 ∧
      [2, 2, 5, 5, 17, 700277].Forall
        (fun q => (2 : ZMod 1190470901) ^ ((1190470901 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_2_0
  · simp only [List.forall_cons]
    have h1 : (1190470900 : ZMod 1190470901) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (1024009807 : ZMod 1190470901) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (520341107 : ZMod 1190470901) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (1027742841 : ZMod 1190470901) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_2_1, modpow_2_2, modpow_2_3, modpow_2_4,
      h1, h2, h3, h4]

/- Lucas certificate 3: modulus 23879310566597711. -/
def bits_3_0 : List Bool := [false, true, true, true, false, false, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, false, true, false, true]

theorem modpow_3_0 : (17 : ZMod 23879310566597711) ^ 23879310566597710 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 17 23879310566597711 23879310566597710 1 bits_3_0
  · norm_num [bits_3_0, bitsValue]
  · norm_num [bits_3_0, natPowModBits]

def bits_3_1 : List Bool := [true, true, true, false, false, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, false, true, false, true]

theorem modpow_3_1 : (17 : ZMod 23879310566597711) ^ 11939655283298855 = 23879310566597710 := by
  apply zmod_pow_eq_of_natPowModBits 17 23879310566597711 11939655283298855 23879310566597710 bits_3_1
  · norm_num [bits_3_1, bitsValue]
  · norm_num [bits_3_1, natPowModBits]

def bits_3_2 : List Bool := [false, true, true, false, true, true, true, false, false, true, false, true, true, true, false, true, false, true, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, true, true, true, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true]

theorem modpow_3_2 : (17 : ZMod 23879310566597711) ^ 4775862113319542 = 23272269573639826 := by
  apply zmod_pow_eq_of_natPowModBits 17 23879310566597711 4775862113319542 23272269573639826 bits_3_2
  · norm_num [bits_3_2, bitsValue]
  · norm_num [bits_3_2, natPowModBits]

def bits_3_3 : List Bool := [false, true, false, false, false, false, true, true, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false, false, true, false, true, true, true, true, false, false, false, false, false, true, true]

theorem modpow_3_3 : (17 : ZMod 23879310566597711) ^ 3411330080942530 = 4665485479398040 := by
  apply zmod_pow_eq_of_natPowModBits 17 23879310566597711 3411330080942530 4665485479398040 bits_3_3
  · norm_num [bits_3_3, bitsValue]
  · norm_num [bits_3_3, natPowModBits]

def bits_3_4 : List Bool := [false, true, true, true, true, true, true, true, false, true, false, true, true, false, false, false, false, false, false, true, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, false, true]

theorem modpow_3_4 : (17 : ZMod 23879310566597711) ^ 83332963070 = 9570503190901195 := by
  apply zmod_pow_eq_of_natPowModBits 17 23879310566597711 83332963070 9570503190901195 bits_3_4
  · norm_num [bits_3_4, bitsValue]
  · norm_num [bits_3_4, natPowModBits]

def bits_3_5 : List Bool := [false, true, true, false, true, false, true, false, false, true, false, false, true, false, false, false, false, true, false, false, true, true, false, false, true]

theorem modpow_3_5 : (17 : ZMod 23879310566597711) ^ 20058710 = 1725431713743623 := by
  apply zmod_pow_eq_of_natPowModBits 17 23879310566597711 20058710 1725431713743623 bits_3_5
  · norm_num [bits_3_5, bitsValue]
  · norm_num [bits_3_5, natPowModBits]

theorem lucas_hcheck_3 :
    ((17 : ZMod 23879310566597711) ^ (23879310566597711 - 1) = 1 ∧
      [2, 5, 7, 286553, 1190470901].Forall
        (fun q => (17 : ZMod 23879310566597711) ^ ((23879310566597711 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_3_0
  · simp only [List.forall_cons]
    have h1 : (23879310566597710 : ZMod 23879310566597711) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (23272269573639826 : ZMod 23879310566597711) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (4665485479398040 : ZMod 23879310566597711) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (9570503190901195 : ZMod 23879310566597711) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h5 : (1725431713743623 : ZMod 23879310566597711) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_3_1, modpow_3_2, modpow_3_3, modpow_3_4, modpow_3_5,
      h1, h2, h3, h4, h5]

/- Lucas certificate 4: modulus 907413801530713019. -/
def bits_4_0 : List Bool := [false, true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, false, true, true, false, false, false, false, true, false, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, false, false, true, false, false, true, true, true, true, true, false, true, false, false, true, false, false, true, true]

theorem modpow_4_0 : (2 : ZMod 907413801530713019) ^ 907413801530713018 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 2 907413801530713019 907413801530713018 1 bits_4_0
  · norm_num [bits_4_0, bitsValue]
  · norm_num [bits_4_0, natPowModBits]

def bits_4_1 : List Bool := [true, false, true, true, true, false, true, true, true, false, false, false, true, true, false, false, true, true, false, false, false, false, true, false, false, false, true, true, true, true, false, true, true, false, true, false, false, false, false, false, false, false, true, false, false, true, true, true, true, true, false, true, false, false, true, false, false, true, true]

theorem modpow_4_1 : (2 : ZMod 907413801530713019) ^ 453706900765356509 = 907413801530713018 := by
  apply zmod_pow_eq_of_natPowModBits 2 907413801530713019 453706900765356509 907413801530713018 bits_4_1
  · norm_num [bits_4_1, bitsValue]
  · norm_num [bits_4_1, natPowModBits]

def bits_4_2 : List Bool := [false, true, true, true, true, false, false, true, false, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, false, false, false, false, true, true, false, true, false, true, true, false, false, true, false, true, false, true]

theorem modpow_4_2 : (2 : ZMod 907413801530713019) ^ 47758621133195422 = 510650586923210145 := by
  apply zmod_pow_eq_of_natPowModBits 2 907413801530713019 47758621133195422 510650586923210145 bits_4_2
  · norm_num [bits_4_2, bitsValue]
  · norm_num [bits_4_2, natPowModBits]

def bits_4_3 : List Bool := [false, true, true, false, false, true]

theorem modpow_4_3 : (2 : ZMod 907413801530713019) ^ 38 = 274877906944 := by
  apply zmod_pow_eq_of_natPowModBits 2 907413801530713019 38 274877906944 bits_4_3
  · norm_num [bits_4_3, bitsValue]
  · norm_num [bits_4_3, natPowModBits]

theorem lucas_hcheck_4 :
    ((2 : ZMod 907413801530713019) ^ (907413801530713019 - 1) = 1 ∧
      [2, 19, 23879310566597711].Forall
        (fun q => (2 : ZMod 907413801530713019) ^ ((907413801530713019 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_4_0
  · simp only [List.forall_cons]
    have h1 : (907413801530713018 : ZMod 907413801530713019) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (510650586923210145 : ZMod 907413801530713019) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (274877906944 : ZMod 907413801530713019) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_4_1, modpow_4_2,
      h1, h2, h3]

/- Lucas certificate 5: modulus 8221702988651068092612692539039. -/
def bits_5_0 : List Bool := [false, true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, false, true, false, false, false, true, false, true, true, true, true, false, false, true, true, false, false, true, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, false, true, false, true, true, false, true, true, true, true, false, false, false, false, false, true, false, true, false, true, false, false, false, false, false, true, true, true, false, true, false, false, false, true, true, true, true, true, false, false, true, true]

theorem modpow_5_0 : (3 : ZMod 8221702988651068092612692539039) ^ 8221702988651068092612692539038 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 3 8221702988651068092612692539039 8221702988651068092612692539038 1 bits_5_0
  · norm_num [bits_5_0, bitsValue]
  · norm_num [bits_5_0, natPowModBits]

def bits_5_1 : List Bool := [true, true, true, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, true, false, true, false, false, false, true, false, true, true, true, true, false, false, true, true, false, false, true, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, true, false, true, false, true, true, false, false, true, false, true, true, false, true, true, true, true, false, false, false, false, false, true, false, true, false, true, false, false, false, false, false, true, true, true, false, true, false, false, false, true, true, true, true, true, false, false, true, true]

theorem modpow_5_1 : (3 : ZMod 8221702988651068092612692539039) ^ 4110851494325534046306346269519 = 8221702988651068092612692539038 := by
  apply zmod_pow_eq_of_natPowModBits 3 8221702988651068092612692539039 4110851494325534046306346269519 8221702988651068092612692539038 bits_5_1
  · norm_num [bits_5_1, bitsValue]
  · norm_num [bits_5_1, natPowModBits]

def bits_5_2 : List Bool := [false, true, false, true, false, false, false, true, true, true, true, false, false, true, false, true, false, false, false, true, true, true, false, true, false, false, false, true, false, true, false, false, false, true, false, false, false, true, false, true, false, true, true, false, true, false, false, false, true, true, false, false, true, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, false, true, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, true, false, true, true, true, false, true, false, false, true, false, true, false, false, false, true]

theorem modpow_5_2 : (3 : ZMod 8221702988651068092612692539039) ^ 2740567662883689364204230846346 = 784771994154734632713183425113 := by
  apply zmod_pow_eq_of_natPowModBits 3 8221702988651068092612692539039 2740567662883689364204230846346 784771994154734632713183425113 bits_5_2
  · norm_num [bits_5_2, bitsValue]
  · norm_num [bits_5_2, natPowModBits]

def bits_5_3 : List Bool := [false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, false, true, false, true, false, true, false, false, true, true, true, true, true, true, true, false, true, false, true, false, false, false, true, false, false, true, true, true, false, true, false, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, true, false, true, true, false, false, false, true, true, false, false, true, false, true, true, false, true, true, true]

theorem modpow_5_3 : (3 : ZMod 8221702988651068092612692539039) ^ 1174528998378724013230384648434 = 6214203107407929155226018619409 := by
  apply zmod_pow_eq_of_natPowModBits 3 8221702988651068092612692539039 1174528998378724013230384648434 6214203107407929155226018619409 bits_5_3
  · norm_num [bits_5_3, bitsValue]
  · norm_num [bits_5_3, natPowModBits]

def bits_5_4 : List Bool := [false, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false, false, true, false, false, false, false, false, true, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, true, true, true, false, false, true, false, true, true, false, false, false, true, true, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, true, true, false, false, false, false, true, true]

theorem modpow_5_4 : (3 : ZMod 8221702988651068092612692539039) ^ 58939896544278695652202566 = 1784669990523847308026008772224 := by
  apply zmod_pow_eq_of_natPowModBits 3 8221702988651068092612692539039 58939896544278695652202566 1784669990523847308026008772224 bits_5_4
  · norm_num [bits_5_4, bitsValue]
  · norm_num [bits_5_4, natPowModBits]

def bits_5_5 : List Bool := [false, true, false, true, false, false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, true, true, false, false, true, true, false, true, false, true, false, true, true, false, false, true, false, true, false, false, true, false, true, false, true, true, true, false, false, false, true, false, true, false, false, true, true, false, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true]

theorem modpow_5_5 : (3 : ZMod 8221702988651068092612692539039) ^ 37213894784575582840853898 = 7624094625029097465708201026239 := by
  apply zmod_pow_eq_of_natPowModBits 3 8221702988651068092612692539039 37213894784575582840853898 7624094625029097465708201026239 bits_5_5
  · norm_num [bits_5_5, bitsValue]
  · norm_num [bits_5_5, natPowModBits]

def bits_5_6 : List Bool := [false, true, false, true, true, true, true, true, false, true, true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true, true, true, true, false, false, false, false, false, true]

theorem modpow_5_6 : (3 : ZMod 8221702988651068092612692539039) ^ 9060588427002 = 1070546724385686914147941823445 := by
  apply zmod_pow_eq_of_natPowModBits 3 8221702988651068092612692539039 9060588427002 1070546724385686914147941823445 bits_5_6
  · norm_num [bits_5_6, bitsValue]
  · norm_num [bits_5_6, natPowModBits]

theorem lucas_hcheck_5 :
    ((3 : ZMod 8221702988651068092612692539039) ^ (8221702988651068092612692539039 - 1) = 1 ∧
      [2, 3, 7, 7, 139493, 220931, 907413801530713019].Forall
        (fun q => (3 : ZMod 8221702988651068092612692539039) ^ ((8221702988651068092612692539039 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_5_0
  · simp only [List.forall_cons]
    have h1 : (8221702988651068092612692539038 : ZMod 8221702988651068092612692539039) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (784771994154734632713183425113 : ZMod 8221702988651068092612692539039) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (6214203107407929155226018619409 : ZMod 8221702988651068092612692539039) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (1784669990523847308026008772224 : ZMod 8221702988651068092612692539039) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h5 : (7624094625029097465708201026239 : ZMod 8221702988651068092612692539039) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h6 : (1070546724385686914147941823445 : ZMod 8221702988651068092612692539039) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_5_1, modpow_5_2, modpow_5_3, modpow_5_4, modpow_5_5, modpow_5_6,
      h1, h2, h3, h4, h5, h6]

/- Lucas certificate 6: modulus 597359177. -/
def bits_6_0 : List Bool := [false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, false, true, true, false, false, true, true, true, false, false, false, true]

theorem modpow_6_0 : (5 : ZMod 597359177) ^ 597359176 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 5 597359177 597359176 1 bits_6_0
  · norm_num [bits_6_0, bitsValue]
  · norm_num [bits_6_0, natPowModBits]

def bits_6_1 : List Bool := [false, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, false, true, true, false, false, true, true, true, false, false, false, true]

theorem modpow_6_1 : (5 : ZMod 597359177) ^ 298679588 = 597359176 := by
  apply zmod_pow_eq_of_natPowModBits 5 597359177 298679588 597359176 bits_6_1
  · norm_num [bits_6_1, bitsValue]
  · norm_num [bits_6_1, natPowModBits]

def bits_6_2 : List Bool := [false, false, false, true, false, false, false, false, true, false, false, false, true, false, true, false, false, true, true, true, true, false, true, true]

theorem modpow_6_2 : (5 : ZMod 597359177) ^ 14569736 = 541515679 := by
  apply zmod_pow_eq_of_natPowModBits 5 597359177 14569736 541515679 bits_6_2
  · norm_num [bits_6_2, bitsValue]
  · norm_num [bits_6_2, natPowModBits]

def bits_6_3 : List Bool := [false, false, false, true, false, true, true, false, true, false, true, false, true, true, true, true, true, false, true, true]

theorem modpow_6_3 : (5 : ZMod 597359177) ^ 914792 = 220973782 := by
  apply zmod_pow_eq_of_natPowModBits 5 597359177 914792 220973782 bits_6_3
  · norm_num [bits_6_3, bitsValue]
  · norm_num [bits_6_3, natPowModBits]

def bits_6_4 : List Bool := [false, false, false, true, false, true, false, true, false, false, true, false, false, false, true, false, true, true]

theorem modpow_6_4 : (5 : ZMod 597359177) ^ 214184 = 448611897 := by
  apply zmod_pow_eq_of_natPowModBits 5 597359177 214184 448611897 bits_6_4
  · norm_num [bits_6_4, bitsValue]
  · norm_num [bits_6_4, natPowModBits]

theorem lucas_hcheck_6 :
    ((5 : ZMod 597359177) ^ (597359177 - 1) = 1 ∧
      [2, 2, 2, 41, 653, 2789].Forall
        (fun q => (5 : ZMod 597359177) ^ ((597359177 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_6_0
  · simp only [List.forall_cons]
    have h1 : (597359176 : ZMod 597359177) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (541515679 : ZMod 597359177) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (220973782 : ZMod 597359177) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (448611897 : ZMod 597359177) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_6_1, modpow_6_2, modpow_6_3, modpow_6_4,
      h1, h2, h3, h4]

/- Lucas certificate 7: modulus 8352730279367. -/
def bits_7_0 : List Bool := [false, true, true, false, false, false, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false, true, true, false, false, true, true, true, true]

theorem modpow_7_0 : (5 : ZMod 8352730279367) ^ 8352730279366 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 5 8352730279367 8352730279366 1 bits_7_0
  · norm_num [bits_7_0, bitsValue]
  · norm_num [bits_7_0, natPowModBits]

def bits_7_1 : List Bool := [true, true, false, false, false, true, true, true, false, true, true, false, true, true, false, true, false, true, false, false, false, false, true, true, false, true, false, false, false, true, true, false, false, false, true, true, false, false, true, true, true, true]

theorem modpow_7_1 : (5 : ZMod 8352730279367) ^ 4176365139683 = 8352730279366 := by
  apply zmod_pow_eq_of_natPowModBits 5 8352730279367 4176365139683 8352730279366 bits_7_1
  · norm_num [bits_7_1, bitsValue]
  · norm_num [bits_7_1, natPowModBits]

def bits_7_2 : List Bool := [false, true, false, false, true, false, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true]

theorem modpow_7_2 : (5 : ZMod 8352730279367) ^ 759339116306 = 7231728308683 := by
  apply zmod_pow_eq_of_natPowModBits 5 8352730279367 759339116306 7231728308683 bits_7_2
  · norm_num [bits_7_2, bitsValue]
  · norm_num [bits_7_2, natPowModBits]

def bits_7_3 : List Bool := [false, true, true, false, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false, false, false, true]

theorem modpow_7_3 : (5 : ZMod 8352730279367) ^ 137017606 = 5311424680632 := by
  apply zmod_pow_eq_of_natPowModBits 5 8352730279367 137017606 5311424680632 bits_7_3
  · norm_num [bits_7_3, bitsValue]
  · norm_num [bits_7_3, natPowModBits]

def bits_7_4 : List Bool := [false, true, true, false, true, false, true, true, false, true, true, false, true, true, true, false, false, false, true, false, true]

theorem modpow_7_4 : (5 : ZMod 8352730279367) ^ 1341142 = 5959669220533 := by
  apply zmod_pow_eq_of_natPowModBits 5 8352730279367 1341142 5959669220533 bits_7_4
  · norm_num [bits_7_4, bitsValue]
  · norm_num [bits_7_4, natPowModBits]

theorem lucas_hcheck_7 :
    ((5 : ZMod 8352730279367) ^ (8352730279367 - 1) = 1 ∧
      [2, 11, 60961, 6228073].Forall
        (fun q => (5 : ZMod 8352730279367) ^ ((8352730279367 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_7_0
  · simp only [List.forall_cons]
    have h1 : (8352730279366 : ZMod 8352730279367) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (7231728308683 : ZMod 8352730279367) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (5311424680632 : ZMod 8352730279367) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (5959669220533 : ZMod 8352730279367) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_7_1, modpow_7_2, modpow_7_3, modpow_7_4,
      h1, h2, h3, h4]

/- Lucas certificate 8: modulus 1430667954174411546959. -/
def bits_8_0 : List Bool := [false, true, true, true, false, false, true, false, true, false, false, false, false, true, false, false, false, true, false, false, false, true, false, true, false, false, true, false, false, true, true, false, true, false, false, false, true, false, true, false, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, true, false, false, true]

theorem modpow_8_0 : (7 : ZMod 1430667954174411546959) ^ 1430667954174411546958 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 7 1430667954174411546959 1430667954174411546958 1 bits_8_0
  · norm_num [bits_8_0, bitsValue]
  · norm_num [bits_8_0, natPowModBits]

def bits_8_1 : List Bool := [true, true, true, false, false, true, false, true, false, false, false, false, true, false, false, false, true, false, false, false, true, false, true, false, false, true, false, false, true, true, false, true, false, false, false, true, false, true, false, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, true, false, false, true]

theorem modpow_8_1 : (7 : ZMod 1430667954174411546959) ^ 715333977087205773479 = 1430667954174411546958 := by
  apply zmod_pow_eq_of_natPowModBits 7 1430667954174411546959 715333977087205773479 1430667954174411546958 bits_8_1
  · norm_num [bits_8_1, bitsValue]
  · norm_num [bits_8_1, natPowModBits]

def bits_8_2 : List Bool := [false, true, false, false, false, false, true, true, false, false, true, false, false, false, false, false, false, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, true, false, true, true, true, false, false, true, false, false, false, true, false, true, false, true, true, true, false, true, true, false, true, false, false, false, true, false, true, false, false, false, true, true, false, true]

theorem modpow_8_2 : (7 : ZMod 1430667954174411546959) ^ 204381136310630220994 = 246925497035420300497 := by
  apply zmod_pow_eq_of_natPowModBits 7 1430667954174411546959 204381136310630220994 246925497035420300497 bits_8_2
  · norm_num [bits_8_2, bitsValue]
  · norm_num [bits_8_2, natPowModBits]

def bits_8_3 : List Bool := [false, true, true, false, false, false, false, false, true, false, true, false, false, true, true, false, true, false, false, false, true, false, true, true, false, true, false, false, false, false, true, false, false, true, true, false, false, false, false, false, false, false, true, true, false, false, false, false, true, false, true, false, false, false, true, false, true, true, true, false, true, true, true, true, true, false, true]

theorem modpow_8_3 : (7 : ZMod 1430667954174411546959) ^ 110051381090339349766 = 924589437944289290450 := by
  apply zmod_pow_eq_of_natPowModBits 7 1430667954174411546959 110051381090339349766 924589437944289290450 bits_8_3
  · norm_num [bits_8_3, bitsValue]
  · norm_num [bits_8_3, natPowModBits]

def bits_8_4 : List Bool := [false, true, false, false, false, true, false, true, false, false, false, false, true, false, false, true, true, true, false, true, true, true, true, true, true, true, false, true, false, true, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false, true, false, false, true, false, false, false, true, true, false, false, true, true, false, true]

theorem modpow_8_4 : (7 : ZMod 1430667954174411546959) ^ 1612928922406326434 = 1208771035008224789600 := by
  apply zmod_pow_eq_of_natPowModBits 7 1430667954174411546959 1612928922406326434 1208771035008224789600 bits_8_4
  · norm_num [bits_8_4, bitsValue]
  · norm_num [bits_8_4, natPowModBits]

def bits_8_5 : List Bool := [false, true, true, false, true, true, false, true, true, true, false, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, true, true, true, true, true, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, true, false, true, false, false, true]

theorem modpow_8_5 : (7 : ZMod 1430667954174411546959) ^ 1348414659919332278 = 638036019099333458215 := by
  apply zmod_pow_eq_of_natPowModBits 7 1430667954174411546959 1348414659919332278 638036019099333458215 bits_8_5
  · norm_num [bits_8_5, bitsValue]
  · norm_num [bits_8_5, natPowModBits]

def bits_8_6 : List Bool := [false, true, false, false, false, false, true, false, false, false, true, true, false, false, false, true, true, false, true, false, true, true, false, false, false, true, false, true]

theorem modpow_8_6 : (7 : ZMod 1430667954174411546959) ^ 171281474 = 767758060640669233462 := by
  apply zmod_pow_eq_of_natPowModBits 7 1430667954174411546959 171281474 767758060640669233462 bits_8_6
  · norm_num [bits_8_6, bitsValue]
  · norm_num [bits_8_6, natPowModBits]

theorem lucas_hcheck_8 :
    ((7 : ZMod 1430667954174411546959) ^ (1430667954174411546959 - 1) = 1 ∧
      [2, 7, 13, 887, 1061, 8352730279367].Forall
        (fun q => (7 : ZMod 1430667954174411546959) ^ ((1430667954174411546959 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_8_0
  · simp only [List.forall_cons]
    have h1 : (1430667954174411546958 : ZMod 1430667954174411546959) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (246925497035420300497 : ZMod 1430667954174411546959) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (924589437944289290450 : ZMod 1430667954174411546959) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (1208771035008224789600 : ZMod 1430667954174411546959) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h5 : (638036019099333458215 : ZMod 1430667954174411546959) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h6 : (767758060640669233462 : ZMod 1430667954174411546959) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_8_1, modpow_8_2, modpow_8_3, modpow_8_4, modpow_8_5, modpow_8_6,
      h1, h2, h3, h4, h5, h6]

/- Lucas certificate 9: modulus 461667964804357559734387547. -/
def bits_9_0 : List Bool := [false, true, false, true, true, false, true, false, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, false, false, true, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, true, false, false, true, false, true, false, false, false, false, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, true, false, true]

theorem modpow_9_0 : (2 : ZMod 461667964804357559734387547) ^ 461667964804357559734387546 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 2 461667964804357559734387547 461667964804357559734387546 1 bits_9_0
  · norm_num [bits_9_0, bitsValue]
  · norm_num [bits_9_0, natPowModBits]

def bits_9_1 : List Bool := [true, false, true, true, false, true, false, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, false, false, true, false, true, true, true, true, false, true, true, false, true, true, false, false, false, false, true, true, true, false, false, true, false, true, false, false, false, false, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true, true, false, true, true, true, true, true, false, true]

theorem modpow_9_1 : (2 : ZMod 461667964804357559734387547) ^ 230833982402178779867193773 = 461667964804357559734387546 := by
  apply zmod_pow_eq_of_natPowModBits 2 461667964804357559734387547 230833982402178779867193773 461667964804357559734387546 bits_9_1
  · norm_num [bits_9_1, bitsValue]
  · norm_num [bits_9_1, natPowModBits]

def bits_9_2 : List Bool := [false, true, false, true, true, true, false, true, true, true, true, false, false, false, true, true, true, false, false, false, true, true, false, true, true, false, true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, true, false, false, true, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, true, false, false, true, true, false, true]

theorem modpow_9_2 : (2 : ZMod 461667964804357559734387547) ^ 27156939106138679984375738 = 45424905876724351289239809 := by
  apply zmod_pow_eq_of_natPowModBits 2 461667964804357559734387547 27156939106138679984375738 45424905876724351289239809 bits_9_2
  · norm_num [bits_9_2, bitsValue]
  · norm_num [bits_9_2, natPowModBits]

def bits_9_3 : List Bool := [false, true, true, true, true, true, true, false, false, false, true, true, false, true, true, false, false, false, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true, true, true, true, false, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false, false, true, false, true, true, false, true, true, true, false, false, true, true, false, false, true, false, false, true, false, true]

theorem modpow_9_3 : (2 : ZMod 461667964804357559734387547) ^ 48642710441929992596606 = 336555126083998082167460020 := by
  apply zmod_pow_eq_of_natPowModBits 2 461667964804357559734387547 48642710441929992596606 336555126083998082167460020 bits_9_3
  · norm_num [bits_9_3, bitsValue]
  · norm_num [bits_9_3, natPowModBits]

def bits_9_4 : List Bool := [false, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, false, false, true]

theorem modpow_9_4 : (2 : ZMod 461667964804357559734387547) ^ 322694 = 54009011080704142550734175 := by
  apply zmod_pow_eq_of_natPowModBits 2 461667964804357559734387547 322694 54009011080704142550734175 bits_9_4
  · norm_num [bits_9_4, bitsValue]
  · norm_num [bits_9_4, natPowModBits]

theorem lucas_hcheck_9 :
    ((2 : ZMod 461667964804357559734387547) ^ (461667964804357559734387547 - 1) = 1 ∧
      [2, 17, 9491, 1430667954174411546959].Forall
        (fun q => (2 : ZMod 461667964804357559734387547) ^ ((461667964804357559734387547 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_9_0
  · simp only [List.forall_cons]
    have h1 : (461667964804357559734387546 : ZMod 461667964804357559734387547) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (45424905876724351289239809 : ZMod 461667964804357559734387547) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (336555126083998082167460020 : ZMod 461667964804357559734387547) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (54009011080704142550734175 : ZMod 461667964804357559734387547) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_9_1, modpow_9_2, modpow_9_3, modpow_9_4,
      h1, h2, h3, h4]

/- Lucas certificate 10: modulus 227868403652723591. -/
def bits_10_0 : List Bool := [false, true, true, false, false, false, false, true, true, true, false, false, false, false, false, true, true, false, false, false, false, false, true, false, true, true, true, false, true, false, false, false, true, true, false, true, true, false, false, false, true, false, true, true, false, false, false, true, true, false, false, true, false, true, false, false, true, true]

theorem modpow_10_0 : (7 : ZMod 227868403652723591) ^ 227868403652723590 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 7 227868403652723591 227868403652723590 1 bits_10_0
  · norm_num [bits_10_0, bitsValue]
  · norm_num [bits_10_0, natPowModBits]

def bits_10_1 : List Bool := [true, true, false, false, false, false, true, true, true, false, false, false, false, false, true, true, false, false, false, false, false, true, false, true, true, true, false, true, false, false, false, true, true, false, true, true, false, false, false, true, false, true, true, false, false, false, true, true, false, false, true, false, true, false, false, true, true]

theorem modpow_10_1 : (7 : ZMod 227868403652723591) ^ 113934201826361795 = 227868403652723590 := by
  apply zmod_pow_eq_of_natPowModBits 7 227868403652723591 113934201826361795 227868403652723590 bits_10_1
  · norm_num [bits_10_1, bitsValue]
  · norm_num [bits_10_1, natPowModBits]

def bits_10_2 : List Bool := [false, true, true, true, false, false, true, false, false, true, false, true, true, false, false, false, true, false, true, true, false, false, false, false, true, true, false, true, false, true, true, false, true, false, true, false, false, false, false, false, true, false, false, true, false, true, true, true, true, false, false, false, false, true, false, true]

theorem modpow_10_2 : (7 : ZMod 227868403652723591) ^ 45573680730544718 = 84725684540274774 := by
  apply zmod_pow_eq_of_natPowModBits 7 227868403652723591 45573680730544718 84725684540274774 bits_10_2
  · norm_num [bits_10_2, bitsValue]
  · norm_num [bits_10_2, natPowModBits]

def bits_10_3 : List Bool := [false, true, false, true, true, true, false, true, true, true, false, false, true, true, true, true, false, false, true, true, true, false, true, false, false, false, true, false, true, true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, true, false, false, false, false, true, false, true, true]

theorem modpow_10_3 : (7 : ZMod 227868403652723591) ^ 7350593666216890 = 124772871918470370 := by
  apply zmod_pow_eq_of_natPowModBits 7 227868403652723591 7350593666216890 124772871918470370 bits_10_3
  · norm_num [bits_10_3, bitsValue]
  · norm_num [bits_10_3, natPowModBits]

def bits_10_4 : List Bool := [false, true, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, true, true, true, false, false, true, false, true, true, true, false, false, true, false, true, true, false, true, false, false, true]

theorem modpow_10_4 : (7 : ZMod 227868403652723591) ^ 5299265201226130 = 170259735504008566 := by
  apply zmod_pow_eq_of_natPowModBits 7 227868403652723591 5299265201226130 170259735504008566 bits_10_4
  · norm_num [bits_10_4, bitsValue]
  · norm_num [bits_10_4, natPowModBits]

def bits_10_5 : List Bool := [false, true, false, false, true, true, false, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true, true, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false, false, true, true, true, false, true, true, false, true, true]

theorem modpow_10_5 : (7 : ZMod 227868403652723591) ^ 3862176333097010 = 125509254039279153 := by
  apply zmod_pow_eq_of_natPowModBits 7 227868403652723591 3862176333097010 125509254039279153 bits_10_5
  · norm_num [bits_10_5, bitsValue]
  · norm_num [bits_10_5, natPowModBits]

def bits_10_6 : List Bool := [false, true, false, false, false, false, false, true, true, true, false, true, false, true, true, true, true, true, false, false, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, false, false, false, false, false, false, true, true, true, false, true, false, false, false, true, true]

theorem modpow_10_6 : (7 : ZMod 227868403652723591) ^ 1739453462997890 = 177742376497552423 := by
  apply zmod_pow_eq_of_natPowModBits 7 227868403652723591 1739453462997890 177742376497552423 bits_10_6
  · norm_num [bits_10_6, bitsValue]
  · norm_num [bits_10_6, natPowModBits]

def bits_10_7 : List Bool := [false, true, false, false, true, false, false, true, true, false, true, false, true, true, true, true, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false, true]

theorem modpow_10_7 : (7 : ZMod 227868403652723591) ^ 48993421555090 = 19855512773610756 := by
  apply zmod_pow_eq_of_natPowModBits 7 227868403652723591 48993421555090 19855512773610756 bits_10_7
  · norm_num [bits_10_7, bitsValue]
  · norm_num [bits_10_7, natPowModBits]

def bits_10_8 : List Bool := [false, true, false, false, false, true, true, false, false, true, true, true, true, false, false, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true]

theorem modpow_10_8 : (7 : ZMod 227868403652723591) ^ 20604792807010 = 13252930440923147 := by
  apply zmod_pow_eq_of_natPowModBits 7 227868403652723591 20604792807010 13252930440923147 bits_10_8
  · norm_num [bits_10_8, bitsValue]
  · norm_num [bits_10_8, natPowModBits]

theorem lucas_hcheck_10 :
    ((7 : ZMod 227868403652723591) ^ (227868403652723591 - 1) = 1 ∧
      [2, 5, 31, 43, 43, 59, 131, 4651, 11059].Forall
        (fun q => (7 : ZMod 227868403652723591) ^ ((227868403652723591 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_10_0
  · simp only [List.forall_cons]
    have h1 : (227868403652723590 : ZMod 227868403652723591) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (84725684540274774 : ZMod 227868403652723591) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (124772871918470370 : ZMod 227868403652723591) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (170259735504008566 : ZMod 227868403652723591) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h5 : (125509254039279153 : ZMod 227868403652723591) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h6 : (177742376497552423 : ZMod 227868403652723591) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h7 : (19855512773610756 : ZMod 227868403652723591) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h8 : (13252930440923147 : ZMod 227868403652723591) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_10_1, modpow_10_2, modpow_10_3, modpow_10_4, modpow_10_5, modpow_10_6, modpow_10_7, modpow_10_8,
      h1, h2, h3, h4, h5, h6, h7, h8]

/- Lucas certificate 11: modulus 186983349423540748034761849124579521373412534080233. -/
def bits_11_0 : List Bool := [false, false, false, true, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, true, false, true, false, true, false, false, true, false, true, false, false, false, false, true, false, false, false, true, false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, false, true, false, false, true, true, false, false, false, false, true, false, false, false, true, false, true, false, false, false, false, false, false, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true]

theorem modpow_11_0 : (5 : ZMod 186983349423540748034761849124579521373412534080233) ^ 186983349423540748034761849124579521373412534080232 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 5 186983349423540748034761849124579521373412534080233 186983349423540748034761849124579521373412534080232 1 bits_11_0
  · norm_num [bits_11_0, bitsValue]
  · norm_num [bits_11_0, natPowModBits]

def bits_11_1 : List Bool := [false, false, true, false, true, true, true, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, true, false, true, false, true, false, false, true, false, true, false, false, false, false, true, false, false, false, true, false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, false, true, false, false, true, true, false, false, false, false, true, false, false, false, true, false, true, false, false, false, false, false, false, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false, true, false, true, true, true, true, false, true, true, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true]

theorem modpow_11_1 : (5 : ZMod 186983349423540748034761849124579521373412534080233) ^ 93491674711770374017380924562289760686706267040116 = 186983349423540748034761849124579521373412534080232 := by
  apply zmod_pow_eq_of_natPowModBits 5 186983349423540748034761849124579521373412534080233 93491674711770374017380924562289760686706267040116 186983349423540748034761849124579521373412534080232 bits_11_1
  · norm_num [bits_11_1, bitsValue]
  · norm_num [bits_11_1, natPowModBits]

def bits_11_2 : List Bool := [false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, false, true, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, false, false, false, false, true, false, true, true, false, false, true, false, true, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true, false, false, false, false, true, true, true, false, true, false, true, true, false, true, false, false, false, true, true, true, true, true, false, false, true, true, false, true, true, false, false, false, false, true, true, false, false, true, true, false, true, false, false, false, false, false, true, true, true, false, true, false, true, false, true, false, false, true, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true]

theorem modpow_11_2 : (5 : ZMod 186983349423540748034761849124579521373412534080233) ^ 62327783141180249344920616374859840457804178026744 = 173582940927843213714450491804636172851439553589787 := by
  apply zmod_pow_eq_of_natPowModBits 5 186983349423540748034761849124579521373412534080233 62327783141180249344920616374859840457804178026744 173582940927843213714450491804636172851439553589787 bits_11_2
  · norm_num [bits_11_2, bitsValue]
  · norm_num [bits_11_2, natPowModBits]

def bits_11_3 : List Bool := [false, false, false, true, true, false, false, false, false, false, false, false, true, true, false, true, false, false, true, true, true, true, true, false, false, false, false, false, true, false, true, false, false, true, true, true, false, false, false, true, false, false, true, true, false, false, true, true, true, true, true, true, true, true, true, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true, false, true, false, false, true, true, false, false, false, true, false, false, false, false, false, false, true, true, false, false, false, false, false, true, true, true, true, false, false, false, true, true, true, true, true, true, true, false, true, true, true, false, false, true, true, false, false, true, false, true, false, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false, true, true, true, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, true]

theorem modpow_11_3 : (5 : ZMod 186983349423540748034761849124579521373412534080233) ^ 6031720949146475743056833842728371657206855938072 = 149936946567178508851199694064331891389820180240674 := by
  apply zmod_pow_eq_of_natPowModBits 5 186983349423540748034761849124579521373412534080233 6031720949146475743056833842728371657206855938072 149936946567178508851199694064331891389820180240674 bits_11_3
  · norm_num [bits_11_3, bitsValue]
  · norm_num [bits_11_3, natPowModBits]

def bits_11_4 : List Bool := [false, false, false, true, false, false, true, false, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false, true, false, true, false, true, false, true, false, false, false, true, true, true, false, false, true, true, true, true, true, true, false, false, true, false, false, false, true, true, false, false, false, true, false, false, false, true, false, true, true, false, true, false, true, true, true, true, false, false, false, false, false, true, true, false, true, false, false, false, true, true, true, true, false, true, true, true, false, true, false, true, true, false, true, true, true, true, false, true, false, false, false, false, false, true, false, true, false, false, true, true, false, false, true, true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true]

theorem modpow_11_4 : (5 : ZMod 186983349423540748034761849124579521373412534080233) ^ 78268459365232627892323921776718091826459830088 = 167335710496423353860864334296937809845562164512202 := by
  apply zmod_pow_eq_of_natPowModBits 5 186983349423540748034761849124579521373412534080233 78268459365232627892323921776718091826459830088 167335710496423353860864334296937809845562164512202 bits_11_4
  · norm_num [bits_11_4, bitsValue]
  · norm_num [bits_11_4, natPowModBits]

def bits_11_5 : List Bool := [false, false, false, true, true, false, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, false, true, true, true, false, true, true, true, false, true, false, false, true, false, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, false, false, true, true, false, false, true, false, false, false, false, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false, false, true, false, true]

theorem modpow_11_5 : (5 : ZMod 186983349423540748034761849124579521373412534080233) ^ 820576027330701996392856176238552 = 11478328818547117970766889925309911000862172349919 := by
  apply zmod_pow_eq_of_natPowModBits 5 186983349423540748034761849124579521373412534080233 820576027330701996392856176238552 11478328818547117970766889925309911000862172349919 bits_11_5
  · norm_num [bits_11_5, bitsValue]
  · norm_num [bits_11_5, natPowModBits]

def bits_11_6 : List Bool := [false, false, false, true, true, true, false, false, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, false, false, false, false, true, false, false, false, true, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, false, true, true, true, true, true, false, false, true, true, false, false, false, false, false, false, false, false, true, false, false, false, true, true, true, false, true, false, true, false, true]

theorem modpow_11_6 : (5 : ZMod 186983349423540748034761849124579521373412534080233) ^ 405016946546809354220856 = 113472515126254763673727347592029861011123047865992 := by
  apply zmod_pow_eq_of_natPowModBits 5 186983349423540748034761849124579521373412534080233 405016946546809354220856 113472515126254763673727347592029861011123047865992 bits_11_6
  · norm_num [bits_11_6, bitsValue]
  · norm_num [bits_11_6, natPowModBits]

theorem lucas_hcheck_11 :
    ((5 : ZMod 186983349423540748034761849124579521373412534080233) ^ (186983349423540748034761849124579521373412534080233 - 1) = 1 ∧
      [2, 2, 2, 3, 31, 2389, 227868403652723591, 461667964804357559734387547].Forall
        (fun q => (5 : ZMod 186983349423540748034761849124579521373412534080233) ^ ((186983349423540748034761849124579521373412534080233 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_11_0
  · simp only [List.forall_cons]
    have h1 : (186983349423540748034761849124579521373412534080232 : ZMod 186983349423540748034761849124579521373412534080233) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (173582940927843213714450491804636172851439553589787 : ZMod 186983349423540748034761849124579521373412534080233) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (149936946567178508851199694064331891389820180240674 : ZMod 186983349423540748034761849124579521373412534080233) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (167335710496423353860864334296937809845562164512202 : ZMod 186983349423540748034761849124579521373412534080233) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h5 : (11478328818547117970766889925309911000862172349919 : ZMod 186983349423540748034761849124579521373412534080233) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h6 : (113472515126254763673727347592029861011123047865992 : ZMod 186983349423540748034761849124579521373412534080233) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_11_1, modpow_11_2, modpow_11_3, modpow_11_4, modpow_11_5, modpow_11_6,
      h1, h2, h3, h4, h5, h6]

/- Lucas certificate 12: modulus 103172769879062304819188940336438602413290547478314441733587841. -/
def bits_12_0 : List Bool := [false, false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, false, true, false, true, false, false, true, true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, true, false, false, false, true, true, false, true, true, false, true, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true, true, false, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, false, true, false, true, false, true, true, false, false, true, true, false, false, true, false, false, false, false, true, false, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false, true, false, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, true]

theorem modpow_12_0 : (3 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ^ 103172769879062304819188940336438602413290547478314441733587840 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 3 103172769879062304819188940336438602413290547478314441733587841 103172769879062304819188940336438602413290547478314441733587840 1 bits_12_0
  · norm_num [bits_12_0, bitsValue]
  · norm_num [bits_12_0, natPowModBits]

def bits_12_1 : List Bool := [false, false, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true, false, false, false, false, true, false, true, false, true, false, false, true, true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false, true, false, false, false, true, true, false, true, true, false, true, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true, true, false, false, true, false, false, true, true, true, true, false, false, true, true, true, true, false, true, false, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, false, true, false, true, false, true, true, false, false, true, true, false, false, true, false, false, false, false, true, false, false, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false, true, false, true, true, false, true, true, false, true, true, true, true, false, true, false, false, false, true, false, true, true, false, false, false, false, false, false, false, false, true]

theorem modpow_12_1 : (3 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ^ 51586384939531152409594470168219301206645273739157220866793920 = 103172769879062304819188940336438602413290547478314441733587840 := by
  apply zmod_pow_eq_of_natPowModBits 3 103172769879062304819188940336438602413290547478314441733587841 51586384939531152409594470168219301206645273739157220866793920 103172769879062304819188940336438602413290547478314441733587840 bits_12_1
  · norm_num [bits_12_1, bitsValue]
  · norm_num [bits_12_1, natPowModBits]

def bits_12_2 : List Bool := [false, false, false, false, false, false, false, true, true, false, true, true, false, false, false, false, false, false, true, false, true, false, false, false, true, true, false, false, true, true, false, false, true, true, false, true, false, false, false, true, true, false, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false, false, true, false, false, false, true, false, true, false, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, true, false, false, false, false, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true, false, true, true, true, true, true, true, false, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true, false, false, true, false, true, false, true, false, false, false, false, true, true, true, false, true, true, false, false, true, false, true, true, false, true, false, false, false, false, true, true, false, true, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false, false, false, true, false, true, true, true, false, true, false, true, true, false, false, true, true]

theorem modpow_12_2 : (3 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ^ 20634553975812460963837788067287720482658109495662888346717568 = 1986402759803028433998580336497950652118255368818728238945286 := by
  apply zmod_pow_eq_of_natPowModBits 3 103172769879062304819188940336438602413290547478314441733587841 20634553975812460963837788067287720482658109495662888346717568 1986402759803028433998580336497950652118255368818728238945286 bits_12_2
  · norm_num [bits_12_2, bitsValue]
  · norm_num [bits_12_2, natPowModBits]

def bits_12_3 : List Bool := [false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, true, true, false, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, true, false, false, false, false, false, false, true, true, false, false, false, false, false, true, false, false, true, true, true, true, false, false, true, true, true, false, false, true, false, true, true, true, true, false, false, true, true, false, true, false, true, false, false, true, true, false, false, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, false, true, false, false, false, false, false, true, false, false, true, true, true, true, true, true, true, false, false, true, false, false, false, true, false, false, false, true, true, false, false, true, true, true, false, true, false, false, false, false, true, false, true, false, true, true, true, false, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false, true, true, true, false, true, true, false, false, true, true, false, false, false, true, true, false, true, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, false, true]

theorem modpow_12_3 : (3 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ^ 14738967125580329259884134333776943201898649639759205961941120 = 90041015792481196199509140335466816061376981227311331959217225 := by
  apply zmod_pow_eq_of_natPowModBits 3 103172769879062304819188940336438602413290547478314441733587841 14738967125580329259884134333776943201898649639759205961941120 90041015792481196199509140335466816061376981227311331959217225 bits_12_3
  · norm_num [bits_12_3, bitsValue]
  · norm_num [bits_12_3, natPowModBits]

def bits_12_4 : List Bool := [false, false, false, false, false, false, false, true, true, true, false, false, true, true, true, true, false, false, false, true, false, false, false, false, false, false, true, true, true, true, true, false, true, false, false, true, false, true, false, false, false, false, true, false, true, true, false, true, true, false, false, false, false, false, true, false, true, false, false, false, true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, true, true, true, false, false, true, false, true, false, true, false, true, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true, true, false, false, true, true, false, false, false, true, true, false, false, false, true, false, false, true, true, false, true, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true]

theorem modpow_12_4 : (3 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ^ 1063636802876930977517411756045758787765881932766128265294720 = 15443518588972269241457976799683149382625405965607683933396828 := by
  apply zmod_pow_eq_of_natPowModBits 3 103172769879062304819188940336438602413290547478314441733587841 1063636802876930977517411756045758787765881932766128265294720 15443518588972269241457976799683149382625405965607683933396828 bits_12_4
  · norm_num [bits_12_4, bitsValue]
  · norm_num [bits_12_4, natPowModBits]

def bits_12_5 : List Bool := [false, false, false, false, false, false, false, true, true, false, true, true, true, true, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true, false, false, true, false, true, true, true, false, true, false, true, false, true, true, true, false, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, false, false, false, true, false, false, false, true, true, true, false, false, true, true, false, true, false, false, false, false, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, true, true, false, true, true, true, false, false, false, true, false, true, false, true, true, true, false, false, true, true, false, true, true, false, true, false, false, true, true, true, false, false, true, false, true, false, false, false, true, false, false, true, false, true, true, false, true, true, true, true, true, true, true, false, false, true, false, true, false, false, true, true, false, false, false, true, true, false, true, false, false, false, false, false, true, false, true, false, true, true]

theorem modpow_12_5 : (3 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ^ 81255484325493867465986109155577276808030150809906052480 = 15598126086374405967558118893141986949300604621907219038131152 := by
  apply zmod_pow_eq_of_natPowModBits 3 103172769879062304819188940336438602413290547478314441733587841 81255484325493867465986109155577276808030150809906052480 15598126086374405967558118893141986949300604621907219038131152 bits_12_5
  · norm_num [bits_12_5, bitsValue]
  · norm_num [bits_12_5, natPowModBits]

def bits_12_6 : List Bool := [false, false, false, false, false, false, false, true, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, false, false, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true]

theorem modpow_12_6 : (3 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ^ 551775172480 = 69079520612912102173999459647599149773213367677531918084134646 := by
  apply zmod_pow_eq_of_natPowModBits 3 103172769879062304819188940336438602413290547478314441733587841 551775172480 69079520612912102173999459647599149773213367677531918084134646 bits_12_6
  · norm_num [bits_12_6, bitsValue]
  · norm_num [bits_12_6, natPowModBits]

theorem lucas_hcheck_12 :
    ((3 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ^ (103172769879062304819188940336438602413290547478314441733587841 - 1) = 1 ∧
      [2, 2, 2, 2, 2, 2, 2, 5, 7, 97, 1269733, 186983349423540748034761849124579521373412534080233].Forall
        (fun q => (3 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ^ ((103172769879062304819188940336438602413290547478314441733587841 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_12_0
  · simp only [List.forall_cons]
    have h1 : (103172769879062304819188940336438602413290547478314441733587840 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (1986402759803028433998580336497950652118255368818728238945286 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (90041015792481196199509140335466816061376981227311331959217225 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (15443518588972269241457976799683149382625405965607683933396828 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h5 : (15598126086374405967558118893141986949300604621907219038131152 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h6 : (69079520612912102173999459647599149773213367677531918084134646 : ZMod 103172769879062304819188940336438602413290547478314441733587841) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_12_1, modpow_12_2, modpow_12_3, modpow_12_4, modpow_12_5, modpow_12_6,
      h1, h2, h3, h4, h5, h6]

/- Lucas certificate 13: modulus 6910083712423065615559090169408100783675718253484998976398609599303612568353159. -/
def bits_13_0 : List Bool := [false, true, true, false, false, false, false, true, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false, true, true, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, true, false, false, false, false, false, false, true, false, false, false, true, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, true, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, true, false, false, false, true, false, false, true, false, false, false, true, false, false, true, true, false, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, true, true, false, true, true, false, false, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, false, true, true, false, true, true, true, true, false, false, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, false, true, true, true, false, true, true, true]

theorem modpow_13_0 : (3 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ^ 6910083712423065615559090169408100783675718253484998976398609599303612568353158 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 3 6910083712423065615559090169408100783675718253484998976398609599303612568353159 6910083712423065615559090169408100783675718253484998976398609599303612568353158 1 bits_13_0
  · norm_num [bits_13_0, bitsValue]
  · norm_num [bits_13_0, natPowModBits]

def bits_13_1 : List Bool := [true, true, false, false, false, false, true, true, false, false, true, true, true, false, true, false, true, false, false, false, true, true, false, true, false, true, true, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, false, true, false, false, false, false, false, false, true, false, false, false, true, true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, true, true, true, true, false, false, false, false, false, false, false, false, true, true, false, true, true, false, false, true, true, true, false, true, true, true, true, true, false, false, true, true, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, false, false, false, true, true, true, false, false, false, true, false, false, true, false, false, false, true, false, false, true, true, false, false, true, false, false, true, true, true, false, false, true, true, true, false, false, false, true, true, true, true, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, true, true, false, true, true, false, false, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, false, true, true, false, true, true, true, true, false, false, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, false, true, false, true, true, false, true, false, true, true, true, false, true, true, true]

theorem modpow_13_1 : (3 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ^ 3455041856211532807779545084704050391837859126742499488199304799651806284176579 = 6910083712423065615559090169408100783675718253484998976398609599303612568353158 := by
  apply zmod_pow_eq_of_natPowModBits 3 6910083712423065615559090169408100783675718253484998976398609599303612568353159 3455041856211532807779545084704050391837859126742499488199304799651806284176579 6910083712423065615559090169408100783675718253484998976398609599303612568353158 bits_13_1
  · norm_num [bits_13_1, bitsValue]
  · norm_num [bits_13_1, natPowModBits]

def bits_13_2 : List Bool := [false, true, false, false, false, false, false, true, false, false, false, true, false, true, true, true, false, false, false, false, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false, false, false, false, false, false, false, true, true, false, true, true, true, false, false, false, false, true, false, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true, false, false, false, true, false, true, false, false, true, false, false, true, false, false, true, true, false, true, true, true, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, true, true, true, true, true, false, true, false, true, false, true, false, true, false, false, true, false, true, false, false, true, false, false, false, false, true, false, false, false, true, false, true, true, true, false, true, true, false, true, false, false, true, true, true, true, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, false, false, false, true, false, true, true, false, false, false, true, false, false, true, true, true, true, true, false, false, true]

theorem modpow_13_2 : (3 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ^ 2303361237474355205186363389802700261225239417828332992132869866434537522784386 = 1598834239679917729056326302426339573015704721362528210347888168663290576099110 := by
  apply zmod_pow_eq_of_natPowModBits 3 6910083712423065615559090169408100783675718253484998976398609599303612568353159 2303361237474355205186363389802700261225239417828332992132869866434537522784386 1598834239679917729056326302426339573015704721362528210347888168663290576099110 bits_13_2
  · norm_num [bits_13_2, bitsValue]
  · norm_num [bits_13_2, natPowModBits]

def bits_13_3 : List Bool := [false, true, false, true, false, true, true, false, false, false, false, false, true, false, true, true, false, false, false, false, true, true, false, false, true, true, true, true, true, true, true, false, true, true, false, false, true, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, false, true, true, true, false, false, true, false, true, false, true, true, true, false, true, false, true, true, true, false, true, false, true, false, false, true, true, false, true, false, false, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, true, false, true, false, false, false, false, true, true, true, true, false, true, false, false, true, false, true, true, false, false, true, true, true, true, true, true, false, true, true, true, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, true, true, false, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, false, true, true, false, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, true, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, true, true, true, true, true, false, true, false, true, true, false, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, false, false, true, true, false, false, true, false, true]

theorem modpow_13_3 : (3 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ^ 300438422279263722415612616061221773203292097977608651147765634752330981232746 = 4224856221757400972506877215944793544195958860965847595798598201244935676297194 := by
  apply zmod_pow_eq_of_natPowModBits 3 6910083712423065615559090169408100783675718253484998976398609599303612568353159 300438422279263722415612616061221773203292097977608651147765634752330981232746 4224856221757400972506877215944793544195958860965847595798598201244935676297194 bits_13_3
  · norm_num [bits_13_3, bitsValue]
  · norm_num [bits_13_3, natPowModBits]

def bits_13_4 : List Bool := [false, true, true, true, false, false, false, false, true, true, false, false, true, true, true, false, true, true, false, false, false, false, true, false, true, true, true, false, true, true, false, true, true, true, false, false, false, false, false, false, true, false, false, false, false, false, true, true, true, true, false, false, true, false, true, true, true, true, true, false, true, false, false, true, true, false, false, true, false, true, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, true, true, false, false, true, true, true, true, true, true, true, true, false, true, true, false, false, true, true, false, false, true, false, false, true, false, true, true, false, false, true, false, true, false, false, false, true, false, true, true, true, true, false, true, true, false, false, true, false, true, false, true, true, true, false, false, true, true, true, false, true, true, false, true, false, false, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, true, false, true, false, false, true, false, true, false, false, false, true, true, false, true, false, false, false, true, false, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, false, false, true, true, true, false, false, true, true, true]

theorem modpow_13_4 : (3 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ^ 25515317174159557846544729431647105592534250495659490868132861186184278798 = 1565304701786974482142557297176509836564729039247387244730838189852635808553895 := by
  apply zmod_pow_eq_of_natPowModBits 3 6910083712423065615559090169408100783675718253484998976398609599303612568353159 25515317174159557846544729431647105592534250495659490868132861186184278798 1565304701786974482142557297176509836564729039247387244730838189852635808553895 bits_13_4
  · norm_num [bits_13_4, bitsValue]
  · norm_num [bits_13_4, natPowModBits]

def bits_13_5 : List Bool := [false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, false, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, false, false, false, true, true, false, false, false, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, false, false, true, false, false, false, true, true, false, true, true, false, true, false, false, false, true, false, true, true, false, false, true, false, false, false, false, true, true, false, false, true, true, false, true, true, true, true, false, false, true, true, false, true, false, false, false, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, false, false, true, false, false, true, true, false, true, true, false, true, true, true, false, false, true, true, false, true, false, false, true, true, false, false, false, true, true, false, false, true, false, true, false, false, true, true, true, false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, true, false, true, true, false, true, true, false, false, false, true, false, true, false, true, true, true, true, true, false, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, false, true, true, false, false, false, true, false, false, false, false, true, false, false, true, false, false, false, true, false, true, true, false, true, false, true, true]

theorem modpow_13_5 : (3 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ^ 11567720022526858435723153156493820440086280374470582505839044972608854 = 4353123858592448720705214698836232186934394729292363292301192736735884003763794 := by
  apply zmod_pow_eq_of_natPowModBits 3 6910083712423065615559090169408100783675718253484998976398609599303612568353159 11567720022526858435723153156493820440086280374470582505839044972608854 4353123858592448720705214698836232186934394729292363292301192736735884003763794 bits_13_5
  · norm_num [bits_13_5, bitsValue]
  · norm_num [bits_13_5, natPowModBits]

def bits_13_6 : List Bool := [false, true, true, false, false, false, false, true, false, false, true, false, false, true, true, false, true, false, false, true, false, false, false, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, false, false, true, false, false, true, true, true, true, true, false, true, true, false, true, true, true]

theorem modpow_13_6 : (3 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ^ 66975847605167238 = 5209693341395459055083600446629104828978936343499843089146733516072058328327938 := by
  apply zmod_pow_eq_of_natPowModBits 3 6910083712423065615559090169408100783675718253484998976398609599303612568353159 66975847605167238 5209693341395459055083600446629104828978936343499843089146733516072058328327938 bits_13_6
  · norm_num [bits_13_6, bitsValue]
  · norm_num [bits_13_6, natPowModBits]

theorem lucas_hcheck_13 :
    ((3 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ^ (6910083712423065615559090169408100783675718253484998976398609599303612568353159 - 1) = 1 ∧
      [2, 3, 3, 23, 270821, 597359177, 103172769879062304819188940336438602413290547478314441733587841].Forall
        (fun q => (3 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ^ ((6910083712423065615559090169408100783675718253484998976398609599303612568353159 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_13_0
  · simp only [List.forall_cons]
    have h1 : (6910083712423065615559090169408100783675718253484998976398609599303612568353158 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (1598834239679917729056326302426339573015704721362528210347888168663290576099110 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (4224856221757400972506877215944793544195958860965847595798598201244935676297194 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (1565304701786974482142557297176509836564729039247387244730838189852635808553895 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h5 : (4353123858592448720705214698836232186934394729292363292301192736735884003763794 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h6 : (5209693341395459055083600446629104828978936343499843089146733516072058328327938 : ZMod 6910083712423065615559090169408100783675718253484998976398609599303612568353159) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_13_1, modpow_13_2, modpow_13_3, modpow_13_4, modpow_13_5, modpow_13_6,
      h1, h2, h3, h4, h5, h6]

/- Lucas certificate 14: modulus 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879. -/
def bits_14_0 : List Bool := [false, true, true, true, false, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false, false, false, true, false, true, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, true, true, true, false, false, false, true, false, true, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, true, false, false, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false, false, true, true, false, false, false, true, true, false, false, false, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false, false, false, false, true, false, false, true, true, false, true, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, false, true, false, true, true, true, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, true, true, true, true, true, true, false, true, false, false, true, true, false, true, true, false, false, true, false, true, true, true, false, true, false, false, false, false, false, false, false, true, false, true, false, true, false, false, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true, false, true, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false, false, false, true, false, false, true, true, false, false, true, false, false, true, false, false, false, true, true, false, true]

theorem modpow_14_0 : (3 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ^ 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356878 = 1 := by
  apply zmod_pow_eq_of_natPowModBits 3 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356878 1 bits_14_0
  · norm_num [bits_14_0, bitsValue]
  · norm_num [bits_14_0, natPowModBits]

def bits_14_1 : List Bool := [true, true, true, false, false, false, false, true, true, true, false, false, false, false, true, true, true, false, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, true, false, false, false, true, false, true, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, true, false, true, true, false, false, false, true, true, false, true, true, true, true, true, false, false, false, true, false, true, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false, true, true, false, false, false, true, true, true, false, true, true, false, true, false, false, false, true, true, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, true, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, true, true, true, true, false, true, false, false, true, true, false, false, false, true, true, false, false, false, true, true, false, false, false, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false, false, false, false, true, false, false, true, true, false, true, false, false, false, false, false, false, false, false, false, false, true, true, false, true, false, false, true, false, true, true, true, true, true, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, false, false, true, true, false, true, false, false, true, false, false, false, false, true, true, true, true, true, true, false, true, false, false, true, true, false, true, true, false, false, true, false, true, true, true, false, true, false, false, false, false, false, false, false, true, false, true, false, true, false, false, false, false, false, true, true, true, true, true, false, true, false, false, false, true, true, true, true, false, true, true, true, true, true, true, true, false, false, true, false, true, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, true, true, true, false, false, false, true, false, false, false, true, false, false, true, true, false, false, true, false, false, true, false, false, false, true, true, false, true]

theorem modpow_14_1 : (3 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ^ 7674640651519550653385207247181463272962119206571789674815812193129762929668024068990349527020084574625353313895947931266906178439 = 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356878 := by
  apply zmod_pow_eq_of_natPowModBits 3 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 7674640651519550653385207247181463272962119206571789674815812193129762929668024068990349527020084574625353313895947931266906178439 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356878 bits_14_1
  · norm_num [bits_14_1, bitsValue]
  · norm_num [bits_14_1, natPowModBits]

def bits_14_2 : List Bool := [false, true, false, true, true, false, true, false, false, true, false, false, false, false, false, true, false, true, true, false, false, false, true, true, true, false, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, false, true, false, true, false, true, true, false, true, true, false, false, false, true, true, true, false, false, false, true, false, false, true, true, true, false, false, false, false, false, true, true, false, false, true, false, false, false, true, false, true, true, false, false, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false, true, false, true, false, true, true, true, true, false, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, false, true, true, true, false, true, false, false, true, true, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, false, true, false, false, true, true, false, false, true, true, false, true, true, true, false, true, false, false, true, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, false, false, false, true, false, false, true, false, false, false, true, true, false, false, false, true, true, false, false, false, true, true, false, true, false, false, false, false, true, false, false, true, true, false, true, false, true, false, true, false, true, false, false, true, true, true, false, true, true, false, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false, true, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true, false, true, true, false, true, false, true, true, true, true, true, true, true, false, false, false, false, true, false, false, true, false, false, false, true, true, true, true, true, false, false, false, false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false, true, false, true, false, true, true, true, false, true, false, false, true, false, true, true, true, true, true, true, true, true, true, false, true, true, false, false, false, false, false, true, true, true, false, true, true, false, false, true, true, true, true, true, true, true, false, true, false, false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true, false, true, true, true]

theorem modpow_14_2 : (3 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ^ 5116427101013033768923471498120975515308079471047859783210541462086508619778682712660233018013389716416902209263965287511270785626 = 1083367198871124871219448249342618724153855412121998505425531555379339032406093157575532716226002013548824490416361116791544500084 := by
  apply zmod_pow_eq_of_natPowModBits 3 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 5116427101013033768923471498120975515308079471047859783210541462086508619778682712660233018013389716416902209263965287511270785626 1083367198871124871219448249342618724153855412121998505425531555379339032406093157575532716226002013548824490416361116791544500084 bits_14_2
  · norm_num [bits_14_2, bitsValue]
  · norm_num [bits_14_2, natPowModBits]

def bits_14_3 : List Bool := [false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, false, false, false, true, false, true, true, false, false, true, false, true, false, true, true, false, true, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false, true, true, true, false, true, false, false, true, true, false, true, false, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true, true, false, false, false, true, false, false, false, false, false, true, true, false, true, true, false, true, false, true, true, true, false, false, false, true, false, false, false, true, false, true, false, false, false, true, false, true, true, false, false, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true, false, false, true, false, false, true, true, true, true, true, true, true, true, false, false, true, false, false, false, true, true, false, true, true, false, true, true, false, false, false, false, false, true, false, true, false, false, false, true, true, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, true, true, true, true, true, false, true, false, false, false, true, true, false, true, false, false, false, false, false, true, true, false, false, true, true, true, true, false, true, true, false, false, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false, false, false, false, true, true, true, true, false, false, false, true, false, false, true, false, true, true, false, true, false, false, false, true, false, false, true, true, false, false, true, true, true, false, true, true, false, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, false, false, false, false, true, false, false, true, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, false, false, false, false, false, false, true, true, false, false, true, true, true, true, true, false, false, false, true, false, false, false, false, false, true, true, true, false, false, true, false, true, true, true, false, false, true, false, true, false, false, true, true]

theorem modpow_14_3 : (3 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ^ 2192754471862728758110059213480418077989176916163368478518803483751360837048006876854385579148595592750100946827413694647687479554 = 8412224090851192568106940375376870732728336668714931206540415765709590544813638725478198723938876215444144590966837714635476668575 := by
  apply zmod_pow_eq_of_natPowModBits 3 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 2192754471862728758110059213480418077989176916163368478518803483751360837048006876854385579148595592750100946827413694647687479554 8412224090851192568106940375376870732728336668714931206540415765709590544813638725478198723938876215444144590966837714635476668575 bits_14_3
  · norm_num [bits_14_3, bitsValue]
  · norm_num [bits_14_3, natPowModBits]

def bits_14_4 : List Bool := [false, true, false, true, false, true, true, true, true, true, true, false, true, false, false, true, true, true, true, false, false, false, false, false, true, true, false, true, true, false, false, true, false, false, false, false, true, false, false, true, false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, true, false, true, true, false, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, true, false, true, true, true, true, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, false, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, true, true, true, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false, true, false, true, true, true, false, true, false, false, false, true, true, false, true, false, false, false, true, true, true, true, false, true, true, false, false, true, true, true, false, true, false, false, true, true, false, false, true, true, false, false, false, false, true, true, false, false, true, true, false, false, false, true, false, false, false, true, true, false, false, true, false, true, false, false, false, false, false, true, true, true, false, false, true, true, false, false, true, false, true, false, true, false, true, true, false, false, true, false, true, true, true, true, false, true, true, false, false, true, false, true, true, true, false, true, false, false, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, false, false, true, true, true, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, true, true, false, true, true, false, false, false, true, false, true, true, false, true, true, false, false, false, false, false, false, false, false, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, false, true, false, false, false, false, true, false, true, true, false, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, false, true, true, false, false, false, false, false, true, false, false, false, true, false, true, true, false, false, false, false, false, false, false, true, true, false, true, false, true, true, false, false, false, false, false, false, false, true]

theorem modpow_14_4 : (3 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ^ 1395389209367191027888219499487538776902203492103961759057420398750865987212368012543699914003651740840973329799263260230346577898 = 13428266313142208559154394307227214665805854150423260536722315154413095625833763850312112853355327915022113641358756100952274097001 := by
  apply zmod_pow_eq_of_natPowModBits 3 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 1395389209367191027888219499487538776902203492103961759057420398750865987212368012543699914003651740840973329799263260230346577898 13428266313142208559154394307227214665805854150423260536722315154413095625833763850312112853355327915022113641358756100952274097001 bits_14_4
  · norm_num [bits_14_4, bitsValue]
  · norm_num [bits_14_4, natPowModBits]

def bits_14_5 : List Bool := [false, true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, false, false, true, true, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, false, true, true, true, false, true, true, false, true, false, false, false, false, false, true, true, true, true, true, true, true, false, true, true, true, false, false, true, false, true, false, false, true, true, true, false, false, true, true, true, false, false, true, false, false, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false, false, false, false, false, false, false, true, true, false, true, false, false, false, false, false, true, false, false, true, true, false, false, false, false, false, false, true, false, false, true, false, false, true, false, true, false, false, false, false, false, true, true, false, true, true, false, false, false, false, true, true, false, false, false, true, true, false, false, false, true, false, true, false, false, false, false, true, false, false, false, false, true, false, false, true, true, true, true, false, true, true, false, false, true, false, false, false, true, true, true, false, false, true, true, true, false, true, true, true, true, false, true, false, true, false, true, true, false, false, true, false, true, true, true, false, true, true, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, true, true, true, false, false, true, true, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false, false, false, true, true, true, false, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, false, true, false, false, false, true, true, true, true, false, true, true, false, false, true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, false, true, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true, true, true, false, false, false, false, false, false, false, true, false, true, false, true, true, true, false, true, false, true]

theorem modpow_14_5 : (3 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ^ 26247447030539097277069639960583829845207367246221691990657649235963666816045461058757841040610059540064471080862 = 2569850003275675856977019558704211921189536197568340441373195988813199107846819902596439674996110782286160325639336391405083527097 := by
  apply zmod_pow_eq_of_natPowModBits 3 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 26247447030539097277069639960583829845207367246221691990657649235963666816045461058757841040610059540064471080862 2569850003275675856977019558704211921189536197568340441373195988813199107846819902596439674996110782286160325639336391405083527097 bits_14_5
  · norm_num [bits_14_5, bitsValue]
  · norm_num [bits_14_5, natPowModBits]

def bits_14_6 : List Bool := [false, true, false, false, true, true, false, false, false, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, true, false, false, false, true, false, true, false, true, true, true, true, false, false, false, true, true, true, true, true, true, false, false, true, true, true, true, false, true, true, false, false, false, false, false, true, false, false, true, false, false, true, true, true, true, true, false, true, true, false, false, false, false, true, true, true, false, true, true, false, false, true, true, false, false, false, false, true, false, false, true, false, true, true, false, false, false, true, true, false, false, false, false, false, true, false, true, false, false, false, true, false, false, false, false, true, true, false, false, true, true, true, false, false, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, true, true, false, false, false, true, false, true, false, true, true, true, false, true, true, false, false, true, true, true, false, false, true, true, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, false, true, false, true, true, true, false, false, true, true, false, true, true, true, true, false, false, false, true, true, false, false, true, false, false, true, false, false, false, true, true, true, true, false, true, false, false, false, false, false, false, true, true, false, true, true, false, false, false, false, false, false, false, false, true, false, true, true, true, true, true, true, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, false, false, false, true, false, false, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, false, true, false, false, true, true, false, false, false, true, false, true, true, false, true, false, true, true, false, true, false, false, false, false, true, false, false, false, false, false, true, false, true, false, true, true, false, true, true]

theorem modpow_14_6 : (3 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ^ 1866922379004286126909178934853688882462318726409208619926043285586928680185792037880021761255089202 = 14629491540600467205655378048663956562947732001142767748847333891275293518345203558372563552455642199399596783357084147359894650818 := by
  apply zmod_pow_eq_of_natPowModBits 3 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 1866922379004286126909178934853688882462318726409208619926043285586928680185792037880021761255089202 14629491540600467205655378048663956562947732001142767748847333891275293518345203558372563552455642199399596783357084147359894650818 bits_14_6
  · norm_num [bits_14_6, bitsValue]
  · norm_num [bits_14_6, natPowModBits]

def bits_14_7 : List Bool := [false, true, false, false, false, false, false, false, false, false, true, true, false, false, true, false, false, true, true, false, true, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, true, false, true, true, false, false, true, true, true, false, false, true, false, false, false, false, false, true, false, false, true, true, false, false, true, false, true, true, true, true, true, false, true, false, true, false, true, false, true, false, false, false, true, false, true, true, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true, true, true, true, false, true, true, false, false, true, false, true, true, true, false, false, false, false, false, false, true, true, true, false, false, true, false, false, false, false, false, false, true, false, true, true, true, false, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, false, true]

theorem modpow_14_7 : (3 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ^ 2221287316019616843259014926487726999783423285283842 = 3122966631773036338422935237522141312934064577250655995926064752551757464506236510760060994365601554616507816860182934851750216063 := by
  apply zmod_pow_eq_of_natPowModBits 3 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 2221287316019616843259014926487726999783423285283842 3122966631773036338422935237522141312934064577250655995926064752551757464506236510760060994365601554616507816860182934851750216063 bits_14_7
  · norm_num [bits_14_7, bitsValue]
  · norm_num [bits_14_7, natPowModBits]

theorem lucas_hcheck_14 :
    ((3 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ^ (15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 - 1) = 1 ∧
      [2, 3, 7, 11, 584791400290477769, 8221702988651068092612692539039, 6910083712423065615559090169408100783675718253484998976398609599303612568353159].Forall
        (fun q => (3 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ^ ((15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 - 1) / q) ≠ 1)) := by
  constructor
  · norm_num only
    exact modpow_14_0
  · simp only [List.forall_cons]
    have h1 : (15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356878 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h2 : (1083367198871124871219448249342618724153855412121998505425531555379339032406093157575532716226002013548824490416361116791544500084 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h3 : (8412224090851192568106940375376870732728336668714931206540415765709590544813638725478198723938876215444144590966837714635476668575 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h4 : (13428266313142208559154394307227214665805854150423260536722315154413095625833763850312112853355327915022113641358756100952274097001 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h5 : (2569850003275675856977019558704211921189536197568340441373195988813199107846819902596439674996110782286160325639336391405083527097 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h6 : (14629491540600467205655378048663956562947732001142767748847333891275293518345203558372563552455642199399596783357084147359894650818 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    have h7 : (3122966631773036338422935237522141312934064577250655995926064752551757464506236510760060994365601554616507816860182934851750216063 : ZMod 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879) ≠ 1 :=
      zmod_natCast_ne_one _ _ (by norm_num) (by norm_num) (by norm_num)
    norm_num only
    simp [modpow_14_1, modpow_14_2, modpow_14_3, modpow_14_4, modpow_14_5, modpow_14_6, modpow_14_7,
      h1, h2, h3, h4, h5, h6, h7]

end OeisA100474.KernelModular
