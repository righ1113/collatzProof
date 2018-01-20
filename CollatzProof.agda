module CollatzProof where

open import Data.Nat

-- 偽
data ⊥ : Set where
-- 真
record ⊤ : Set where

-- 選言
data _∨_ (P Q : Set) : Set where
  ∨Intro1 : P → P ∨ Q
  ∨Intro2 : Q → P ∨ Q
∨Elim : {P Q R : Set} → P ∨ Q  →  (P → R) → (Q → R) → R
∨Elim (∨Intro1 a) prfP _ = prfP a
∨Elim (∨Intro2 b) _ prfQ = prfQ b

-- 含意
data _⊃_ (P Q : Set) : Set where
  ⊃Intro : (P → Q) → P ⊃ Q
⊃Elim : {P Q : Set} → P ⊃ Q → P → Q
⊃Elim (⊃Intro x) q = x q
 
-- 否定
¬ : Set → Set
¬ p = p ⊃ ⊥
⊥Elim : {P : Set} → ⊥ → P
⊥Elim ()

postulate
  LEM : (P : Set) → (P ∨ ¬ P)
  smaller : ℕ → Set
  -- n:左端からの連続するビット1
  -- n+1で小さくならない→nで小さくならない
  lemma1-3 : (n : ℕ) → ¬ (smaller (suc n)) → ¬ (smaller n)
  lemma2   : smaller zero -- evenは小さくなる
  lemma3   : smaller 1    -- 4x+1は小さくなる

-- 三段論法
syllogism : {A B C : Set} → (A → B) → (B → C) → (A → C)
syllogism x y z = y (x z)

-- 対偶1
contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition = λ x x₁ →
  let z = ⊃Elim x₁ ; y = syllogism x z in ⊃Intro y

-- 二重否定除去
DNE : (P : Set) → ¬ (¬ P) ⊃ P
DNE p = ⊃Intro (λ x → ∨Elim (LEM p) (λ y → y) (λ z → ⊥Elim (⊃Elim x z)))
DNE2 : {p : Set} → p → ¬ (¬ p)
DNE2 p  = ⊃Intro λ x → let y = ⊃Elim x in y p
DNE3 : {p : Set} → ¬ (¬ p) → p
DNE3 {p0} p1 = let f = ⊃Elim (DNE p0) in f p1

-- 対偶2
contraposition2 : {A B : Set} → (¬ B → ¬ A) → (A → B)
contraposition2 p a =
  let t = (contraposition p) (DNE2 a) in DNE3 t

-- 本論
-- n:最下位からの連続するビット1
proof : (n : ℕ) → smaller n
proof zero       = lemma2 -- even
proof (suc zero) = lemma3 -- 4x+1
proof (suc n)    = part n (proof n)
  where
    -- （n+1で小さくならない→nで小さくならない）→（nで小さくなる→n+1で小さくなる）
    part : (n : ℕ) → smaller n → smaller (suc n)
    part n = contraposition2 (lemma1-3 n)
