module nouse_CollatzProof where

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

-- 否定
¬ : Set → Set
¬ p = p → ⊥
⊥Elim : {P : Set} → ⊥ → P
⊥Elim ()

postulate
  LEM : (P : Set) → (P ∨ ¬ P)
  smaller : ℕ → Set
  -- n:左端からの連続するビット1
  -- k+2で小さくならない→k+1で小さくならない
  lemma1-3 : (k : ℕ) → ¬ (smaller (suc (suc k))) → ¬ (smaller (suc k))
  lemma2   : smaller 0 -- evenは小さくなる
  lemma3   : smaller 1 -- 4x+1は小さくなる

-- 二重否定除去
DNE1 : {p : Set} → p → ¬ (¬ p)
DNE1 p q = q p
DNE2 : {p : Set} → ¬ (¬ p) → p
DNE2 {p0} p1 = ∨Elim (LEM p0) (λ y → y) (λ z → ⊥Elim (p1 z))

-- 対偶
contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition = λ f g x → g (f x)
contraposition2 : {A B : Set} → (¬ B → ¬ A) → (A → B)
contraposition2 p a =
  let t = (contraposition p) (DNE1 a) in DNE2 t

-- 本論
-- n:最下位からの連続するビット1
proof : (n : ℕ) → smaller n
proof zero          = lemma2 -- even
proof (suc zero)    = lemma3 -- 4x+1
proof (suc (suc n)) = part n (proof (suc n))
  where
    -- （k+2で小さくならない→k+1で小さくならない）→（k+1で小さくなる→k+2で小さくなる）
    part : (k : ℕ) → smaller (suc k) → smaller (suc (suc k))
    part k = contraposition2 (lemma1-3 k)



