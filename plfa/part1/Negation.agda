module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_)
open import plfa.part1.Connectives using (extensionality)

-- Negation

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

-- Exercise <-irreflexive (recommended)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s n<n) = <-irreflexive n<n

-- Exercise trichotomy (practice)

<-¬> : ∀ {m n : ℕ} → m < n → ¬ (n < m)
<-¬> (s<s m<n) (s<s n<m) = <-¬> m<n n<m

pred : ∀ (n : ℕ) → ℕ
pred 0 = 0
pred (suc n) = n

<-≢ : ∀ {m n : ℕ} → m < n → ¬ (m ≡ n)
<-≢ (s<s m<n) sm≡sn = <-≢ m<n (cong pred sm≡sn)

≡-¬< : ∀ {m n : ℕ} → m ≡ n → ¬ (m < n)
≡-¬< m≡n m<n = <-≢ m<n m≡n

≡-¬> : ∀ {m n : ℕ} → m ≡ n → ¬ (n < m)
≡-¬> m≡n n<m = <-≢ n<m (sym m≡n)

-- Exercise ⊎-dual-× (recommended)

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
    { to = λ{ f → ⟨ (λ{ x → (f (inj₁ x)) }) , (λ{ y → (f (inj₂ y)) }) ⟩ }
    ; from = λ{ ⟨ ¬x , ¬y ⟩ →
               λ{ (inj₁ x) → (¬x x)
                ; (inj₂ y) → (¬y y)
                }
              }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ ¬x , ¬y ⟩ → refl }
    }

¬⊎-to-×¬ : ∀ {A B : Set} → ¬ A ⊎ ¬ B → ¬ (A × B)
¬⊎-to-×¬ (inj₁ ¬x) ⟨ x , y ⟩ = ¬x x
¬⊎-to-×¬ (inj₂ ¬y) ⟨ x , y ⟩ = ¬y y

-- Excluded middle is irrefutable

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable f = f (inj₂ λ{ x → (f (inj₁ x)) })

-- Exercise Classical (stretch)

module em where
    postulate
        em : ∀ {A : Set} → A ⊎ ¬ A

    dne : ∀ {A : Set} → ¬ ¬ A → A
    dne ¬¬x with em
    ...        | inj₁ x = x
    ...        | inj₂ ¬x = ⊥-elim (¬¬x ¬x)

    peirce : ∀ {A B : Set} → ((A → B) → A) → A
    peirce g with em
    ...         | inj₁ x = x
    ...         | inj₂ ¬x = g λ{ x → ⊥-elim (¬x x) }

    →-as-⊎ : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
    →-as-⊎ f with em
    ...       | inj₁ x = inj₂ (f x)
    ...       | inj₂ ¬x = inj₁ ¬x

    demorgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
    demorgan f with em
    ...           | inj₁ x = inj₁ x
    ...           | inj₂ ¬x with em
    ...                        | inj₁ y = inj₂ y
    ...                        | inj₂ ¬y = ⊥-elim (f ⟨ ¬x , ¬y ⟩ )

module dne where
    postulate
        dne : ∀ {A : Set} → ¬ ¬ A → A

    em : ∀ {A : Set} → A ⊎ ¬ A
    em = dne em-irrefutable

    peirce : ∀ {A B : Set} → ((A → B) → A) → A
    peirce g with em
    ...         | inj₁ x = x
    ...         | inj₂ ¬x = g λ{ x → ⊥-elim (¬x x) }

    →-as-⊎ : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
    →-as-⊎ f with em
    ...       | inj₁ x = inj₂ (f x)
    ...       | inj₂ ¬x = inj₁ ¬x

    demorgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
    demorgan f with em
    ...           | inj₁ x = inj₁ x
    ...           | inj₂ ¬x with em
    ...                        | inj₁ y = inj₂ y
    ...                        | inj₂ ¬y = ⊥-elim (f ⟨ ¬x , ¬y ⟩ )

module peirce where
    postulate
        peirce : ∀ {A B : Set} → ((A → B) → A) → A

    em : ∀ {A : Set} → A ⊎ ¬ A
    em = peirce λ{ f →  inj₂ λ{ x → f (inj₁ x) } }

    dne : ∀ {A : Set} → ¬ ¬ A → A
    dne ¬¬x with em
    ...        | inj₁ x = x
    ...        | inj₂ ¬x = ⊥-elim (¬¬x ¬x)

    →-as-⊎ : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
    →-as-⊎ f with em
    ...       | inj₁ x = inj₂ (f x)
    ...       | inj₂ ¬x = inj₁ ¬x

    demorgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
    demorgan f with em
    ...           | inj₁ x = inj₁ x
    ...           | inj₂ ¬x with em
    ...                        | inj₁ y = inj₂ y
    ...                        | inj₂ ¬y = ⊥-elim (f ⟨ ¬x , ¬y ⟩ )

module →-as-⊎ where
    postulate
        →-as-⊎ : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B

    em : ∀ {A : Set} → A ⊎ ¬ A
    em {A} = helper (→-as-⊎ λ{ x → x })
      where
      helper : ¬ A ⊎ A → A ⊎ ¬ A
      helper (inj₁ ¬x) = inj₂ ¬x
      helper (inj₂ x) = inj₁ x

    dne : ∀ {A : Set} → ¬ ¬ A → A
    dne ¬¬x with em
    ...        | inj₁ x = x
    ...        | inj₂ ¬x = ⊥-elim (¬¬x ¬x)

    peirce : ∀ {A B : Set} → ((A → B) → A) → A
    peirce g with em
    ...         | inj₁ x = x
    ...         | inj₂ ¬x = g λ{ x → ⊥-elim (¬x x) }

    demorgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
    demorgan f with em
    ...           | inj₁ x = inj₁ x
    ...           | inj₂ ¬x with em
    ...                        | inj₁ y = inj₂ y
    ...                        | inj₂ ¬y = ⊥-elim (f ⟨ ¬x , ¬y ⟩ )

module demorgan where
    postulate
        demorgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B

    em : ∀ {A : Set} → A ⊎ ¬ A
    em = demorgan λ{ ⟨ ¬x , ¬¬x ⟩ → ¬¬x ¬x }

    dne : ∀ {A : Set} → ¬ ¬ A → A
    dne ¬¬x with em
    ...        | inj₁ x = x
    ...        | inj₂ ¬x = ⊥-elim (¬¬x ¬x)

    →-as-⊎ : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
    →-as-⊎ f with em
    ...       | inj₁ x = inj₂ (f x)
    ...       | inj₂ ¬x = inj₁ ¬x

    peirce : ∀ {A B : Set} → ((A → B) → A) → A
    peirce g with em
    ...         | inj₁ x = x
    ...         | inj₂ ¬x = g λ{ x → ⊥-elim (¬x x) }

-- Exercise Stable (stretch)

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable = ¬¬¬-elim

×¬¬-to-¬⊎¬ : ∀ {A B : Set} → ¬ ¬ (A × B) → ¬ (¬ A ⊎ ¬ B)
×¬¬-to-¬⊎¬ = contraposition ¬⊎-to-×¬

×¬¬-to-¬¬× : ∀ {A B : Set} → ¬ ¬ (A × B) → (¬ ¬ A) × (¬ ¬ B)
×¬¬-to-¬¬× = (_≃_.to ⊎-dual-×) ∘ ×¬¬-to-¬⊎¬

×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable {A} {B} ¬¬x→-x ¬¬y→-y ¬¬⟨x,y⟩ = ⟨ ¬¬x→-x (proj₁ ⟨¬¬x,¬¬y⟩) , ¬¬y→-y (proj₂ ⟨¬¬x,¬¬y⟩) ⟩
  where
    ⟨¬¬x,¬¬y⟩ : (¬ ¬ A) × (¬ ¬ B)
    ⟨¬¬x,¬¬y⟩ = ×¬¬-to-¬¬× ¬¬⟨x,y⟩
