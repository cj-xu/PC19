
  ========================
  =                      =
  =  §0. A mini library  =
  =                      =
  ========================

     Chuangjie Xu, 2018


This is a mini library to make the Agda development of the paper

  A syntactic approach to continuity of Gödel's system T definable functionals

self-contained.

\begin{code}

module Preliminaries where

\end{code}

■ function composition

\begin{code}

_∘_ : {A : Set} {B : A → Set} {C : {a : A} → B a → Set}
    → ({a : A} (b : B a) → C b) → (f : (a : A) → B a) → (a : A) → C (f a)
f ∘ g = λ a → f (g a)

\end{code}

■ identity types

\begin{code}

data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
 refl : a ≡ a

ap : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A}
      → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

transport : {A : Set} (P : A → Set) {x y : A}
          → x ≡ y → P x → P y
transport P refl p = p

\end{code}

■ (dependent) pairs

\begin{code}

record Σ {A : Set} (B : A → Set) : Set where
 constructor _,_
 field
  pr₁ : A
  pr₂ : B pr₁

open Σ public

infixr 1 _×_ _,_

_×_ : Set → Set → Set
A × B = Σ \(_ : A) → B

data _∨_ (A B : Set) : Set where
 inl : A → A ∨ B
 inr : B → A ∨ B

\end{code}

■ unit type

\begin{code}

data 𝟙 : Set where
 ⋆ : 𝟙

\end{code}

■ natural numbers

\begin{code}

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

rec : {A : Set} → A → (ℕ → A → A) → ℕ → A
rec a f  0       = a
rec a f (succ n) = f n (rec a f n)

_+_ : ℕ → ℕ → ℕ
n + m = rec n (λ _ → succ) m

infix 2 _≤_

data _≤_ : ℕ → ℕ → Set where
 ≤zero : {n : ℕ} → 0 ≤ n
 ≤succ : {n m : ℕ} → n ≤ m → succ n ≤ succ m

≤refl : {n : ℕ} → n ≤ n
≤refl {0}      = ≤zero
≤refl {succ n} = ≤succ ≤refl

≤refl' : {n m : ℕ} → n ≡ m → n ≤ m
≤refl' refl = ≤refl

≤trans : {n m l : ℕ} → n ≤ m → m ≤ l → n ≤ l
≤trans  ≤zero           s  = ≤zero
≤trans (≤succ r) (≤succ s) = ≤succ (≤trans r s)

max : ℕ → ℕ → ℕ
max  0        m       = m
max (succ n)  0       = succ n
max (succ n) (succ m) = succ (max n m)

max-spec₀ : (n m : ℕ) → n ≤ max n m
max-spec₀  0        m       = ≤zero
max-spec₀ (succ n)  0       = ≤refl
max-spec₀ (succ n) (succ m) = ≤succ (max-spec₀ n m)

max-spec₁ : (n m : ℕ) → m ≤ max n m
max-spec₁  0        m       = ≤refl
max-spec₁ (succ n)  0       = ≤zero
max-spec₁ (succ n) (succ m) = ≤succ (max-spec₁ n m)

\end{code}

■ infinite sequences as functions from ℕ

\begin{code}

_ᴺ : Set → Set
A ᴺ = ℕ → A

ℕᴺ : Set
ℕᴺ = ℕ ᴺ

head : {A : Set} → A ᴺ → A
head α = α 0

tail : {A : Set} → A ᴺ → A ᴺ
tail α i = α (succ i)

infixr 1 _✶_

_✶_ : {A : Set} → A → A ᴺ → A ᴺ
(a ✶ α)  0       = a
(a ✶ α) (succ i) = α i

_ʷ : {A : Set} → A → A ᴺ
a ʷ = λ i → a

\end{code}

■ α ≡[ n ] β  expresses that the first n bits of α and β are equal

\begin{code}

data _≡[_]_ {A : Set} : A ᴺ → ℕ → A ᴺ → Set where
 ≡[zero] : {α β : A ᴺ} → α ≡[ 0 ] β
 ≡[succ] : {α β : A ᴺ} {n : ℕ} → head α ≡ head β → tail α ≡[ n ] tail β → α ≡[ succ n ] β

≡[≤] : {A : Set} {α β : A ᴺ} {n m : ℕ}
     → α ≡[ n ] β → m ≤ n → α ≡[ m ] β
≡[≤]  en             ≤zero    = ≡[zero]
≡[≤] (≡[succ] e en) (≤succ r) = ≡[succ] e (≡[≤] en r)

≡[]-< : {A : Set} {α β : A ᴺ} {n i : ℕ}
      → α ≡[ n ] β → succ i ≤ n → α i ≡ β i
≡[]-< (≡[succ] e en) (≤succ ≤zero)     = e
≡[]-< (≡[succ] e en) (≤succ (≤succ r)) = ≡[]-< en (≤succ r)

≡[]-refl : {n : ℕ} {A : Set} {α : A ᴺ}
         → α ≡[ n ] α
≡[]-refl {0}      = ≡[zero]
≡[]-refl {succ n} = ≡[succ] refl ≡[]-refl

\end{code}
