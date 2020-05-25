module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-comm; ≤-refl; +-mono-≤)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Relations using (_<_; z<s; +-mono-<)
open import plfa.part1.Isomorphism using (_≃_)
open import plfa.part1.Connectives using (extensionality)

-- Universals

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

-- Exercise ∀-distrib-× (recommended)

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} { f g : ∀ (x : A) → B x }
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ{ L → ( proj₁ ∘ L , proj₂ ∘ L ) }
    ; from = λ{ ( J , K ) → λ{ M → ( (J M) , (K M) ) } }
    ; from∘to = λ{ L → ∀-extensionality λ{ M → refl } }
    ; to∘from = λ{ ( J , K ) → refl }
    }

-- Exercise ⊎∀-implies-∀⊎ (practice)

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ J) = λ{ M → inj₁ (J M) }
⊎∀-implies-∀⊎ (inj₂ K) = λ{ M → inj₂ (K M) }

-- The converse does not hold. A simple counter example is having A = {0, 1},
-- B 0, and C 1 only. This way, we have ∀ (x : A) → B x ⊎ C x but not
-- ∀ (x : A) → B x because we don't have B 1 and 1 ∈ A.

-- Exercise ∀-× (practice)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

∀-× : ∀ (B : Tri → Set) → (∀ (x : Tri) → B x) ≃ ((B aa × B bb) × B cc)
∀-× B =
  record
    { to = λ{ L → ( ( (L aa) , (L bb) ) , (L cc) ) }
    ; from = λ{ ( ( x , y ) , z ) →
                λ{ aa → x
                 ; bb → y
                 ; cc → z
                 }
              }
    ; from∘to = λ{ L → ∀-extensionality λ{ aa → refl ; bb → refl ; cc → refl } }
    ; to∘from = λ{ ( ( x , y ) , z ) → refl }
    }

-- Existentials

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

-- Exercise ∃-distrib-⊎ (recommended)

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ{ ⟨ x , (inj₁ Bx) ⟩ → (inj₁ ⟨ x , Bx ⟩)
            ; ⟨ x , (inj₂ Cx) ⟩ → (inj₂ ⟨ x , Cx ⟩)
            }
    ; from = λ{ (inj₁ ⟨ x , Bx ⟩) → ⟨ x , (inj₁ Bx) ⟩
              ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , (inj₂ Cx) ⟩
              }
    ; from∘to = λ{ ⟨ x , (inj₁ Bx) ⟩ → refl
                 ; ⟨ x , (inj₂ Cx) ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , Bx ⟩) → refl
                 ; (inj₂ ⟨ x , Cx ⟩) → refl
                 }
    }

-- Exercise ∃×-implies-×∃ (practice)

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ (⟨ x , ( Bx , Cx ) ⟩) = ( ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ )

-- The converse does not hold. Imagine x ∈ {0, 1} and (B 0), (C 1) and ¬(B 1)
-- and ¬(C 0). Therefore, (∃[ x ] B x) × (∃[ x ] C x) but not
-- ∃[ x ] (B x × C x).

-- Exercise ∃-⊎ (practice)

∃-⊎ : ∀ (B : Tri → Set) → (∃[ x ] B x) ≃ ((B aa ⊎ B bb) ⊎ B cc)
∃-⊎ B =
  record
    { to = λ{ ⟨ aa , Bx ⟩ → (inj₁ (inj₁ Bx))
            ; ⟨ bb , Bx ⟩ → (inj₁ (inj₂ Bx))
            ; ⟨ cc , Bx ⟩ → (inj₂ Bx)
            }
    ; from = λ{ (inj₁ (inj₁ Bx)) → ⟨ aa , Bx ⟩
              ; (inj₁ (inj₂ Bx)) → ⟨ bb , Bx ⟩
              ; (inj₂ Bx) → ⟨ cc , Bx ⟩
              }
    ; from∘to = λ{ ⟨ aa , Bx ⟩ → refl
                 ; ⟨ bb , Bx ⟩ → refl
                 ; ⟨ cc , Bx ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ (inj₁ Bx)) → refl
                 ; (inj₁ (inj₂ Bx)) → refl
                 ; (inj₂ Bx) → refl
                 }
    }

-- An existential example

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)


even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩


∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)

-- Exercise ∃-even-odd (practice)

even-lemma-2 : ∀ (n : ℕ) →  n + (n + zero) + 1 ≡ n + suc (n + zero)
even-lemma-2 n =
  begin
    n + (n + zero) + 1
  ≡⟨ +-assoc n (n + zero) 1 ⟩
    n + ((n + zero) + 1)
  ≡⟨ cong (n +_) (+-comm (n + zero) 1) ⟩
    n + suc (n + zero)
  ∎

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
{-# NON_TERMINATING #-}
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n
∃-even′ ⟨ zero , refl ⟩ = even-zero
∃-even′ ⟨ suc m , refl ⟩ = even-suc (∃-odd′ ⟨ m , even-lemma-2 m ⟩)
∃-odd′ ⟨ n , refl ⟩ rewrite +-comm (n + (n + zero)) 1 = odd-suc (∃-even′ ⟨ n , refl ⟩)

-- Exercise ∃-+-≤ (practice)

∃-+-≤ : ∀ {m n : ℕ} → ∃[ k ] (k + m ≡ n) → m ≤ n
∃-+-≤ ⟨ k , refl ⟩ = +-mono-≤ z≤n ≤-refl

≤-+-∃ : ∀ {m n : ℕ} → m ≤ n → ∃[ k ] (k + m ≡ n)
≤-+-∃ {m} {n} z≤n = ⟨ n , +-comm n 0 ⟩
≤-+-∃ (s≤s m≤n) with ≤-+-∃ m≤n
...                | ⟨ k , refl ⟩ = ⟨ k , k+suc-m≡suc-k+m ⟩
  where
    k+suc-m≡suc-k+m : ∀ {k m : ℕ} → k + suc m ≡ suc (k + m)
    k+suc-m≡suc-k+m {k} {m} =
      begin
        k + suc m
      ≡⟨ +-comm k (suc m) ⟩
        suc m + k
      ≡⟨⟩
        suc (m + k)
      ≡⟨ cong suc (+-comm m k) ⟩
        suc (k + m)
      ∎

-- Existentials, Universals, and Negation

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }

-- Exercise ∃¬-implies-¬∀ (recommended)

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ f = ¬Bx (f x)

-- The converse does not hold in intuitionistic logic because we don't know
-- which x is such that ¬ B x.

-- Exercise Bin-isomorphism (stretch)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to 0 = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (bin O) = from bin + from bin
from (bin I) = 1 + from bin + from bin

data One : Bin → Set where
  one :
    ----------
    One (⟨⟩ I)

  add-zero : ∀ {bin : Bin}
    → One bin
    -------------
    → One (bin O)

  add-one : ∀ {bin : Bin}
    → One bin
    -------------
    → One (bin I)

data Can : Bin → Set where
  zero :
    --------
    Can (⟨⟩ O)

  leading-one : ∀ {bin : Bin}
    → One bin
      -------
    → Can bin

inc-preserves-leading-one : ∀ {bin : Bin}
  → One bin
  ---------------
  → One (inc bin)

inc-preserves-leading-one one = add-zero one
inc-preserves-leading-one (add-zero lone) = add-one lone
inc-preserves-leading-one (add-one lone) = add-zero (inc-preserves-leading-one lone)

inc-preserves-can : ∀ {bin : Bin}
  → Can bin
    -------------
  → Can (inc bin)
inc-preserves-can zero = leading-one one
inc-preserves-can (leading-one one) = leading-one (add-zero one)
inc-preserves-can (leading-one (add-zero lone)) = leading-one (add-one lone)
inc-preserves-can (leading-one (add-one lone)) = leading-one (add-zero (inc-preserves-leading-one lone))

to-yields-can : ∀ (n : ℕ) → Can (to n)
to-yields-can zero = zero
to-yields-can (suc n) = inc-preserves-can (to-yields-can n)

to′ : ℕ → ∃[ b ](Can b)
to′ n = ⟨ (to n) , (to-yields-can n) ⟩

from′ : ∃[ b ](Can b) → ℕ
from′ ⟨ b , cb ⟩ = from b

from-inc≡suc-from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc≡suc-from ⟨⟩ = refl
from-inc≡suc-from (b O) = refl
from-inc≡suc-from (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    from (inc b) + from (inc b)
  ≡⟨ cong (from (inc b) +_) (from-inc≡suc-from b) ⟩
    from (inc b) + suc (from b)
  ≡⟨ cong (_+ suc (from b)) (from-inc≡suc-from b) ⟩
    suc (from b) + suc (from b)
  ≡⟨⟩
    suc (from b + suc (from b))
  ≡⟨ cong suc (+-comm (from b) (suc (from b))) ⟩
    2 + (from b + from b)
  ≡⟨⟩
    1 + 1 + (from (b O))
  ≡⟨ +-assoc 1 1 (from (b O)) ⟩
    1 + (1 + (from (b O)))
  ≡⟨⟩
    1 + (suc (from (b O)))
  ≡⟨⟩
    1 + (from (inc (b O)))
  ≡⟨⟩
    1 + (from (b I))
  ≡⟨⟩
    suc (from (b I))
  ∎

from-to : ∀ (n : ℕ) →  from (to n) ≡ n
from-to 0 = refl
from-to (suc n) rewrite from-inc≡suc-from (to n) | from-to n = refl

from′-to′ : ∀ (n : ℕ) →  from′ (to′ n) ≡ n
from′-to′ 0 = refl
from′-to′ (suc n) =
  begin
    from′ (to′ (suc n))
  ≡⟨⟩
    from′ ⟨ (inc (to n)) , (to-yields-can (suc n)) ⟩
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ from-inc≡suc-from (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (from-to n) ⟩
    suc n
  ∎

zero-<-from-one : ∀ (bin : Bin)
  → One bin
     -------------
  → 0 < (from bin)
zero-<-from-one (⟨⟩ I) one = z<s
zero-<-from-one (bin O) (add-zero bin-one) = (+-mono-< 0 (from bin) 0 (from bin) (zero-<-from-one bin bin-one) (zero-<-from-one bin bin-one))
zero-<-from-one (bin I) (add-one bin-one) = z<s

to-suc-n-2-O : ∀ (n : ℕ)
  → 0 < n
     ---------------------
  → to (n + n) ≡ (to n) O
to-suc-n-2-O zero ()
to-suc-n-2-O (suc zero) z<s = refl
to-suc-n-2-O (suc (suc n)) z<s =
  begin
    to (suc (suc n) + suc (suc n))
  ≡⟨⟩
    inc (to (suc n + suc (suc n)))
  ≡⟨ cong inc (cong to (+-comm (suc n) (suc (suc n)))) ⟩
    inc (to (suc (suc n) + suc n))
  ≡⟨⟩
    inc (inc (to (suc n + suc n)))
  ≡⟨ cong inc (cong inc (to-suc-n-2-O (suc n) z<s)) ⟩
    inc (inc (to (suc n) O))
  ≡⟨⟩
    (to (suc (suc n))) O
  ∎

to-from-can≡id : ∀ {bin : Bin}
  → Can bin
     ---------------
  → to (from bin) ≡ bin
to-from-can≡id zero = refl
to-from-can≡id (leading-one one) = refl
to-from-can≡id {bin O} (leading-one (add-zero lone)) =
  begin
    to (from (bin O))
  ≡⟨⟩
    to (from bin + from bin)
  ≡⟨ to-suc-n-2-O (from bin) (zero-<-from-one bin lone) ⟩
    (to (from bin)) O
  ≡⟨ cong (_O) (to-from-can≡id (leading-one lone)) ⟩
    bin O
  ∎
to-from-can≡id {bin I} (leading-one (add-one lone)) =
  begin
    to (from (bin I))
  ≡⟨⟩
    to (1 + from bin + from bin)
  ≡⟨⟩
    to (suc (from bin + from bin))
  ≡⟨⟩
    inc (to (from bin + from bin))
  ≡⟨ cong (inc) (to-suc-n-2-O (from bin) (zero-<-from-one bin lone)) ⟩
    inc ((to (from bin)) O)
  ≡⟨⟩
   (to (from bin)) I
  ≡⟨ cong (_I) (to-from-can≡id (leading-one lone)) ⟩
    bin I
  ∎

≡One : ∀{b : Bin} (o o′ : One b) → o ≡ o′
≡One one one = refl
≡One (add-zero o) (add-zero o′) = cong add-zero (≡One o o′)
≡One (add-one o) (add-one o′) = cong add-one (≡One o o′)

≡Can : ∀ {b : Bin} (cb : Can b) (cb′ : Can b) → cb ≡ cb′
≡Can zero zero = refl
≡Can zero (leading-one (add-zero ()))
≡Can (leading-one (add-zero ())) zero
≡Can (leading-one lone) (leading-one lone′) = cong leading-one (≡One lone lone′)

lemma : ∀ {b b′ : Bin}
    → b ≡ b′
    → (cb : Can b)
    → (cb′ : Can b′)
      -------------------------
    → ⟨ b , cb ⟩ ≡ ⟨ b′ , cb′ ⟩
lemma b≡b′ cb cb′ rewrite b≡b′ | ≡Can cb cb′ = refl

to′-from′ : ∀ (bcb : ∃[ b ](Can b)) →  to′ (from′ bcb) ≡ bcb
to′-from′ ⟨ b , cb ⟩ =
  begin
    to′ (from′ ⟨ b , cb ⟩)
  ≡⟨⟩
    to′ (from b)
  ≡⟨⟩
    ⟨ to (from b) , (to-yields-can (from b)) ⟩
  ≡⟨ lemma (to-from-can≡id cb) (to-yields-can (from b)) cb ⟩
    ⟨ b , cb ⟩
  ∎

Bin-isomorphism : ℕ ≃ ∃[ b ](Can b)
Bin-isomorphism =
  record
    { to = to′
    ; from = from′
    ; from∘to = from′-to′
    ; to∘from = to′-from′
    }
