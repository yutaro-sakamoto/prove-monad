module Interfaces


%default total
-- Define function equality

public export
data FuncEqType : func1 -> func2 -> Type where
  funcEqType : (f : a -> b) -> (g : a -> b) -> ((x : a) -> f x = g x) -> FuncEqType f g

public export
stateFuncEqTransitive : {f : a -> b} -> {g : a -> b} -> {h : a -> b} -> FuncEqType f g -> FuncEqType g h ->  FuncEqType f h
stateFuncEqTransitive (funcEqType f g f_eq_g) (funcEqType g h g_eq_h) = funcEqType f h (\z => rewrite f_eq_g z in g_eq_h z)

public export
stateFuncEqReflexive : {f : a -> b} -> FuncEqType f f
stateFuncEqReflexive = funcEqType f f (\z => Refl)

public export
stateFuncEqSymmetry : FuncEqType a b -> FuncEqType b a
stateFuncEqSymmetry (funcEqType f g a_eq_b) = funcEqType g f (\z => sym (a_eq_b z))

-- Functor Interface

public export
interface MyFunctor (f : Type -> Type) where
  -- equality
  equalsTo : (x : f a) -> (y : f a) -> Type
  eqReflexive : {x : f a} -> x `equalsTo` x
  eqSymmetry : {x, y : f a} -> x `equalsTo` y -> y `equalsTo` x
  eqTransitive :  {x, y, z : f a} -> x `equalsTo` y -> y `equalsTo` z -> x `equalsTo` z

  -- map
  myMap : (func : a -> b) -> (x : f a) -> f b

  -- functor law
  functorLawIdentity : (x : f a) -> myMap Prelude.id x `equalsTo` x
  functorLawComposition : (v : (b -> c)) -> (u : (a -> b)) -> (x : f a) -> myMap (v . u) x `equalsTo` myMap v (myMap u x)

infixl 3 <<*>>

public export
interface MyFunctor f => MyApplicative (f : Type -> Type) where
  myPure : a -> f a
  (<<*>>): f (a -> b) -> f a -> f b

  -- applicative law
  applicativeLawIdentity : (u : f a) ->
    (myPure Prelude.id <<*>> u) `equalsTo` u
  applicativeLawHomomorphism : (x : a) -> (func : a -> b) ->
    (myPure func <<*>> myPure x) `equalsTo` myPure (func x)
  applicativeLawInterchange : (u : f (a -> b)) -> (x : a) ->
    (u <<*>> myPure x) `equalsTo` (myPure ($ x) <<*>> u)
  applicativeLawComposition : (u : f (b -> c)) -> (v : f (a -> b)) -> (w : f a) ->
                              (myPure (\f => \g => \x => f (g x)) <<*>> u <<*>> v <<*>> w) `equalsTo` (u <<*>> (v <<*>> w))

infixl 1 >>>=
public export
interface MyFunctor m => MyMonad (m : Type -> Type) where
  myReturn : a -> m a
  (>>>=) : m a -> (a -> m b) -> m b

  monadLawIdentityLeft : (x : a) -> (f : a -> m b) -> (myReturn x >>>= f) `equalsTo` (f x)
  monadLawIdentityRight : (n : m a) -> (n >>>= myReturn) `equalsTo` n
  monadLawComposition : (n : m a) -> (f : a -> m b) -> (g : b -> m c) ->
                        ((n >>>= f) >>>= g) `equalsTo` (n >>>= \x => f x >>>= g)
