module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Connectives using (extensionality)
open import plfa.part1.Induction using (*-distrib-+)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)

-- Lists

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

{-# BUILTIN LIST List #-}

-- List syntax

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

-- Append

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎

-- Reasoning about append

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

-- Length

length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎

-- Reasoning about length

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

-- Reverse

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

-- Exercise reverse-++-distrib (recommended)

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []
  ≡⟨⟩
    reverse ys ++ reverse []
  ∎
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ (reverse (x ∷ xs))
  ∎

-- Exercise reverse-involutive (recommended)

reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    reverse [ x ] ++ (reverse (reverse xs))
  ≡⟨⟩
    [ x ] ++ (reverse (reverse xs))
  ≡⟨ cong ([ x ] ++_) (reverse-involutive xs) ⟩
    [ x ] ++ xs
  ≡⟨⟩
    x ∷ xs
  ∎

-- Faster reverse

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎

-- Map

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎

-- Exercise map-compose (practice)

map-compose-app : ∀ {A B C : Set}
  → (f : A → B) → (g : B → C) → (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose-app f g [] = refl
map-compose-app f g (x ∷ xs) =
  begin
    map (g ∘ f) (x ∷ xs)
  ≡⟨⟩
    ((g ∘ f) x) ∷ (map (g ∘ f) xs)
  ≡⟨ cong (((g ∘ f) x) ∷_) (map-compose-app f g xs) ⟩
    ((g ∘ f) x) ∷ (((map g) ∘ (map f)) xs)
  ≡⟨⟩
    (g (f x)) ∷ (((map g) ∘ (map f)) xs)
  ≡⟨⟩
    map g ((f x) ∷ (map f xs))
  ≡⟨⟩
    map g (map f (x ∷ xs))
  ≡⟨⟩
    (map g ∘ map f) (x ∷ xs)
  ∎

map-compose : ∀ {A B C : Set}
  → (f : A → B) → (g : B → C) → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality (map-compose-app f g)

-- Exercise map-++-distribute (practice)

map-++-distribute : ∀ {A B : Set}
  → (f : A → B) → (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys =
  begin
    map f ([] ++ ys)
  ≡⟨⟩
    map f ys
  ≡⟨⟩
    map f [] ++ map f ys
  ∎
map-++-distribute f (x ∷ xs) ys =
  begin
    map f ((x ∷ xs) ++ ys)
  ≡⟨⟩
    map f (x ∷ (xs ++ ys))
  ≡⟨⟩
    (f x) ∷ (map f (xs ++ ys))
  ≡⟨ cong ((f x) ∷_) (map-++-distribute f xs ys) ⟩
    (f x) ∷ (map f xs ++ map f ys)
  ≡⟨⟩
    ((f x) ∷ (map f xs)) ++ map f ys
  ≡⟨⟩
    map f (x ∷ xs) ++ map f ys
  ∎

-- Exercise map-Tree (practice)

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node left-child y right-child) =
  node (map-Tree f g left-child) (g y) (map-Tree f g right-child)

-- Fold

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

-- Exercise product (recommended)

product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

-- Exercise foldr-++ (recommended)

foldr-++ : ∀ {A B : Set}
  → (_⊗_ : A → B → B)
  → (e : B)
  → (xs ys : List A)
    ------------------------------------------------------
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin
    foldr _⊗_ e ((x ∷ xs) ++ ys)
  ≡⟨⟩
    foldr _⊗_ e (x ∷ (xs ++ ys))
  ≡⟨⟩
    x ⊗ foldr _⊗_ e (xs ++ ys)
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
    x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨⟩
    foldr _⊗_ (foldr _⊗_ e ys) (x ∷ xs)
  ∎

-- Exercise foldr-∷ (practice)

foldr-∷ : ∀ {A : Set} → (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) =
  begin
    foldr _∷_ [] (x ∷ xs)
  ≡⟨⟩
    x ∷ foldr _∷_ [] xs
  ≡⟨ cong (x ∷_) (foldr-∷ xs) ⟩
    x ∷ xs
  ∎

++-foldr-∷ : ∀ {A : Set} → (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
++-foldr-∷ xs ys rewrite sym (foldr-∷ (xs ++ ys)) | foldr-++ _∷_ [] xs ys | foldr-∷ ys = refl

-- Exercise map-is-foldr (practice)

map-is-foldr-app : ∀ {A B : Set}
  → (f : A → B) → (xs : List A) → map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
map-is-foldr-app f [] = refl
map-is-foldr-app f (x ∷ xs) =
  begin
    map f (x ∷ xs)
  ≡⟨⟩
    (f x) ∷ (map f xs)
  ≡⟨ cong ((f x) ∷_) (map-is-foldr-app f xs) ⟩
    (f x) ∷ (foldr (λ x xs → f x ∷ xs) [] xs)
  ≡⟨⟩
    foldr (λ x xs → f x ∷ xs) [] (x ∷ xs)
  ∎

map-is-foldr : ∀ {A B : Set} → (f : A → B) → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality (map-is-foldr-app f)

-- Exercise fold-Tree (practice)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree leaf-func _ (leaf x) = leaf-func x
fold-Tree leaf-func node-func (node left-child y right-child) =
  node-func (fold-Tree leaf-func node-func left-child) y (fold-Tree leaf-func node-func right-child)

-- Exercise map-is-fold-Tree (practice)

map-is-fold-Tree-app : ∀ {A B C D : Set}
  → (f : A → C) → (g : B → D) → (t : Tree A B)
  → map-Tree f g t ≡ fold-Tree (λ x → leaf (f x)) (λ l y r → (node l (g y) r)) t
map-is-fold-Tree-app f g (leaf x) = refl
map-is-fold-Tree-app f g (node l y r)
  rewrite map-is-fold-Tree-app f g l | map-is-fold-Tree-app f g r = refl

map-is-fold-Tree : ∀ {A B C D : Set}
  → (f : A → C) → (g : B → D)
  → map-Tree f g ≡ fold-Tree (λ x → leaf (f x)) (λ l y r → (node l (g y) r))
map-is-fold-Tree f g = extensionality (map-is-fold-Tree-app f g)

-- Exercise sum-downFrom (stretch)

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

sum-downFrom : ∀ (n : ℕ) →  sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom 0 = refl
sum-downFrom 1 = refl
sum-downFrom (suc (suc n)) =
  begin
    sum (downFrom (suc (suc n))) * 2
  ≡⟨⟩
    sum ((suc n) ∷ downFrom (suc n)) * 2
  ≡⟨⟩
    (suc n + (sum (downFrom (suc n)))) * 2
  ≡⟨ *-distrib-+ (suc n) (sum (downFrom (suc n))) 2 ⟩
    (suc n) * 2 + (sum (downFrom (suc n))) * 2
  ≡⟨ cong (((suc n) * 2) +_) (sum-downFrom (suc n)) ⟩
    (suc n) * 2 + (suc n) * ((suc n) ∸ 1)
  ≡⟨⟩
    (suc n) * 2 + (suc n) * n
  ≡⟨ cong (_+ ((suc n) * n)) (*-comm (suc n) 2) ⟩
    2 * (suc n) + (suc n) * n
  ≡⟨ cong ((2 * (suc n)) +_) (*-comm (suc n) n) ⟩
    2 * (suc n) + n * (suc n)
  ≡⟨ sym (*-distrib-+ 2 n (suc n)) ⟩
    (2 + n) * (suc n)
  ∎

-- Monoids

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

-- Exercise foldl (practice)

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e []        =  e
foldl _⊗_ e (x ∷ xs)  =  foldl _⊗_ (e ⊗ x) xs

-- Exercise foldr-monoid-foldl (practice)

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → y ⊗ foldl _⊗_ e xs ≡ foldl _⊗_ y xs
foldl-monoid _⊗_ e ⊗-monoid [] y = (identityʳ ⊗-monoid) y
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y
  rewrite (identityˡ ⊗-monoid) x
    | sym (foldl-monoid _⊗_ e ⊗-monoid xs x)
    | sym ((assoc ⊗-monoid) y x (foldl _⊗_ e xs))
      = foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x)

foldr-monoid-foldl-app : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl-app _⊗_ e _ [] = refl
foldr-monoid-foldl-app _⊗_ e ⊗-monoid (x ∷ xs) =
  begin
    foldr _⊗_ e (x ∷ xs)
  ≡⟨⟩
    x ⊗ foldr _⊗_ e xs
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl-app _⊗_ e ⊗-monoid xs) ⟩
    x ⊗ foldl _⊗_ e xs
  ≡⟨ cong (_⊗ foldl _⊗_ e xs) (sym ((identityˡ ⊗-monoid) x)) ⟩
    (e ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ foldl-monoid _⊗_ e ⊗-monoid xs (e ⊗ x) ⟩
    foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    foldl _⊗_ e (x ∷ xs)
  ∎

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl _⊗_ e ⊗-monoid = extensionality (foldr-monoid-foldl-app _⊗_ e ⊗-monoid)

-- All

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

-- Any

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

-- All and append

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

-- Exercise Any-++-⇔ (recommended)

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  to [] ys Pys = inj₂ Pys
  to (x ∷ xs) ys (here Px) = inj₁ (here Px)
  to (x ∷ xs) ys (there Pxs++Pys) with to xs ys Pxs++Pys
  ...                                | inj₁ Pxs = inj₁ (there Pxs)
  ...                                | inj₂ Pys = inj₂ Pys

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
  from (x ∷ xs) ys (inj₁ (here Px)) = here Px
  from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
  from [] ys (inj₂ Pys) = Pys
  from (x ∷ xs) ys (inj₂ Pys) = there (from xs ys (inj₂ Pys))

∈-++-⇔ : ∀ {A : Set} (x : A) (xs ys : List A) →
  (x ∈ (xs ++ ys)) ⇔ ((x ∈ xs) ⊎ (x ∈ ys))
∈-++-⇔ x xs ys = Any-++-⇔ xs ys

-- Exercise All-++-≃ (stretch)

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    ; from∘to = from∘to xs ys
    ; to∘from = to∘from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

  from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (all-p-xs-++-ys : (All P (xs ++ ys))) →
    (from xs ys) (to xs ys all-p-xs-++-ys) ≡ all-p-xs-++-ys
  from∘to [] ys Pys = refl
  from∘to (x ∷ xs) ys (Px ∷ Pxs++ys) = cong (Px ∷_) (from∘to xs ys Pxs++ys)

  to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A)
    (all-p-xs-and-all-p-ys : (All P xs × All P ys)) →
    (to xs ys) (from xs ys all-p-xs-and-all-p-ys) ≡ all-p-xs-and-all-p-ys
  to∘from [] ys ⟨ [] , Pys ⟩ = refl
  to∘from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ rewrite to∘from xs ys ⟨ Pxs , Pys ⟩ = refl

-- Exercise ¬Any⇔All¬ (recommended)

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) →
  (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs =
  record
    { to = to xs
    ; from = from xs
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs : List A) →
    (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
  to [] _ = []
  to (x ∷ xs) ¬∘Any-P-xs = (λ{ Px → ¬∘Any-P-xs (here Px) }) ∷ (to xs ¬∘Any-P-xs)
  -- we need to convert the "(¬_ ∘ Any P) (x ∷ xs)" into "(¬_ ∘ Any P) xs"

  from : ∀ {A : Set} {P : A → Set} {xs : List A} →
    All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
  -- from [] = λ{ Any-Px → () }
  from (¬Px ∷ _) (here Px) = ¬Px Px
  from (_ ∷ All-¬P-xs) (there Any-P-xs) = (from All-¬P-xs) Any-P-xs
