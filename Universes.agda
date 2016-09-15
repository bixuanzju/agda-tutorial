module Universes where

data False : Set where
record True : Set where

data Bool : Set where
  true : Bool
  false : Bool

isTrue : Bool → Set
isTrue true = True
isTrue false = False

infix 30 not_
infixr 25 _and_

not_ : Bool → Bool
not true = false
not false = true

_and_ : Bool → Bool → Bool
true and x = x
false and _ = false

notNotId : (a : Bool) → isTrue (not not a) → isTrue a
notNotId true prf = prf
notNotId false ()

data Functor : Set₁ where
  |Id| : Functor
  |K| : Set → Functor
  _|+|_ : Functor → Functor → Functor
  _|*|_ : Functor → Functor → Functor

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 50 _|+|_ _⊕_
infixr 60 _|*|_ _×_

[_] : Functor → Set → Set
[ |Id| ] X = X
[ |K| x ] X = x
[ F |+| G ] X =  [ F ] X ⊕ [ G ] X
[ F |*| G ] X = [ F ] X × [ G ] X

map : (F : Functor) → {X Y : Set} → (X → Y) → [ F ] X → [ F ] Y
map |Id| f x = f x
map (|K| x) f x₁ = x₁
map (F |+| G) f (inl x) =  inl (map F f x)
map (F |+| G) f (inr x) =  inr (map G f x)
map (F |*| G) f (x , y) = (map F f x) , (map G f y)

data μ_ (F : Functor) : Set where
  <_> : [ F ] (μ F) → μ F
