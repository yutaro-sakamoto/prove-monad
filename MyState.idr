import Interfaces

-- State Definition

data State : Type -> Type -> Type where
  stateFunc : (s -> (a, s)) -> State s a

getStateFunc : (state : State s a) -> (s -> (a, s))
getStateFunc (stateFunc f) = f


-- Define state equality


data StateEq : state1 -> state2 -> Type where
  stateEq : {u : State s a} -> {v : State s a} -> (getStateFunc u `FuncEqType` getStateFunc v) -> StateEq u v

stateEqTransitiveLemma : {f : a -> b} -> {g : a -> b} -> {h : a -> b} -> FuncEqType f g -> FuncEqType g h -> (x : a) -> f x = h x
stateEqTransitiveLemma (funcEqType f g f_eq_g) (funcEqType g h g_eq_h) x = rewrite f_eq_g x in g_eq_h x

stateEqTransitive : {f : State s a} -> {g : State s a} -> {h : State s a} -> StateEq f g -> StateEq g h ->  StateEq f h
stateEqTransitive (stateEq x) (stateEq y) = stateEq (funcEqType (getStateFunc f) (getStateFunc h) (stateEqTransitiveLemma x y))

stateEqReflexive : {f : State s a} -> StateEq f f
stateEqReflexive = stateEq (funcEqType (getStateFunc f) (getStateFunc f) (\x => Refl))

stateEqSymmetryLemma : {f : a -> b} -> {g : a -> b} -> FuncEqType f g -> (x : a) -> g x = f x
stateEqSymmetryLemma (funcEqType f g f_eq_g) x = sym (f_eq_g x)

stateEqSymmetry : {f : State s a} -> {g : State s a} -> StateEq f g -> StateEq g f
stateEqSymmetry (stateEq x) = stateEq (funcEqType (getStateFunc g) (getStateFunc f) (stateEqSymmetryLemma x))


-- map for State

mapFirst : (f : a -> c) -> (a, b) -> (c, b)
mapFirst f (x, y) = (f x, y)

mapState : (f : a -> b) -> (state : State s a) -> State s b
mapState f (stateFunc g) = stateFunc (mapFirst f . g)


-- Verify that State is Functor


mapFirstIdLemma : (x : (a, b)) -> mapFirst Prelude.id x = x
mapFirstIdLemma (p, q) = Refl

stateFunctorLawIdentityLemma : (state : State s a) -> (x : s) -> getStateFunc (mapState Prelude.id state) x = getStateFunc state x
stateFunctorLawIdentityLemma (stateFunc f) x = mapFirstIdLemma (f x)

stateFunctorLawIdentity : (state : State s a) -> mapState Prelude.id state `StateEq` state
stateFunctorLawIdentity state = stateEq $ funcEqType (getStateFunc $ mapState Prelude.id state) (getStateFunc state) (stateFunctorLawIdentityLemma state)

mapFirstCompositionLemma : (g : b -> c) -> (h : a -> b) -> (x : (a, s)) -> mapFirst (g . h) x = mapFirst g (mapFirst h x)
mapFirstCompositionLemma g h (p, q) = Refl

stateFunctorLawCompositionLemma : (state : State s a) -> (g : (b -> c)) -> (h : (a -> b)) -> (x : s) -> getStateFunc (mapState (g . h) state) x = getStateFunc (mapState g (mapState h state)) x
stateFunctorLawCompositionLemma (stateFunc f) g h x = rewrite mapFirstCompositionLemma g h (f x)in Refl

stateFunctorLawComposition : (g : (b -> c)) -> (h : (a -> b)) -> (state : State s a) -> mapState (g . h) state `StateEq` mapState g (mapState h state)
stateFunctorLawComposition g h state = stateEq $ funcEqType (getStateFunc $ mapState (g . h) state) (getStateFunc $ mapState g $ mapState h state) (stateFunctorLawCompositionLemma state g h)

MyFunctor (State s) where
  equalsTo = StateEq
  eqReflexive = stateEqReflexive
  eqSymmetry = stateEqSymmetry
  eqTransitive = stateEqTransitive
  myMap = mapState
  functorLawIdentity = stateFunctorLawIdentity
  functorLawComposition = stateFunctorLawComposition


-- Applicative functions


pureState : (s : Type) -> (x : a) -> State s a
pureState s x = stateFunc (\state => (x, state))

infixl 3 <<**>>

(<<**>>) : State s (a -> b) -> State s a -> State s b
(<<**>>) (stateFunc ff) (stateFunc gg) = stateFunc newStateFunc
where
  newStateFunc : (ss : s) -> (b, s)
  newStateFunc ss = mapFirst (fst $ ff ss) (gg $ snd (ff ss))


-- Applicative laws


stateApplicativeLawIdentityLemma : (u : State s a) -> (x : s) -> getStateFunc (stateFunc (\s => (Prelude.id, s)) <<**>> u) x = getStateFunc u x
stateApplicativeLawIdentityLemma (stateFunc f) x = mapFirstIdLemma (f x)

stateApplicativeLawIdentity : (s : Type) -> (u : State s a) -> (pureState s Prelude.id <<**>> u) `StateEq` u
stateApplicativeLawIdentity s u = stateEq $ funcEqType (getStateFunc $ pureState s Prelude.id <<**>> u) (getStateFunc u) (stateApplicativeLawIdentityLemma u)


stateApplicativeLawHomomorphism : (s : Type) -> (x : a) -> (func : a -> b) ->
                                  (pureState s func <<**>> pureState s x) `StateEq` (pureState s (func x))
stateApplicativeLawHomomorphism s x func = stateEq $ funcEqType (getStateFunc $ pureState s func <<**>> pureState s x)
                                                                (getStateFunc $ pureState s (func x))
                                                                (\z => Refl)

mapFirstAppLemma : (f : (a -> b, s)) -> (x : a) -> (fst f x, snd f) = mapFirst ($ x) f
mapFirstAppLemma (func, state) x = Refl

stateApplicativeLawInterchangeLemma : (f : (s -> (a -> b, s))) -> (x : a) -> (state : s) -> (fst (f state) x, snd (f state)) = mapFirst ($ x) (f state)
stateApplicativeLawInterchangeLemma f x state = rewrite mapFirstAppLemma (f state) x in Refl

stateApplicativeLawInterchange : (s : Type) -> (u : State s (a -> b)) -> (x : a) ->
                                 (u <<**>> pureState s x) `StateEq` (pureState s ($ x) <<**>> u)
stateApplicativeLawInterchange s (stateFunc f) x = stateEq $ funcEqType (getStateFunc $ (stateFunc f) <<**>> pureState s x)
                                                                   (getStateFunc $ pureState s ($ x) <<**>> (stateFunc f))
                                                                   (stateApplicativeLawInterchangeLemma f x)

composeStateFunc : (u : State s (b -> c)) -> (v : State s (a -> b)) -> State s (a -> c)
composeStateFunc (stateFunc f) (stateFunc g) = stateFunc h
  where
    h : s -> ((a -> c), s)
    h s = let p = (f s)
              q = g (snd p)
           in (fst p . fst q, snd q)

-- proof of Applicative is incomplete
(s : Type) => MyApplicative (State s) where
  myPure = pureState s
  (<<*>>) = (<<**>>)

  applicativeLawIdentity = stateApplicativeLawIdentity s
  applicativeLawHomomorphism = stateApplicativeLawHomomorphism s
  applicativeLawInterchange = stateApplicativeLawInterchange s
  applicativeLawComposition = ?stateApplicativeLawComposition


-- Monad

infixl 1 >>>==

(>>>==) : (n : State s a) -> (f : a -> State s b) -> State s b
(>>>==) (stateFunc g) f = stateFunc (\state => let x = g state in getStateFunc (f $ fst x) (snd x))

stateReturn : (x : a) -> State s a
stateReturn x = stateFunc (\state => (x, state))

stateMonadLawIdentityLeft : (x : a) -> (f : a -> State s b) -> (stateReturn x >>>== f) `equalsTo` (f x)
stateMonadLawIdentityLeft x f = stateEq $ funcEqType (getStateFunc $ stateReturn x >>>== f) (getStateFunc (f x)) (\z => Refl)

stateMonadLawIdentityRightLemma2 : (z : (a, s)) -> (fst z, snd z) = z
stateMonadLawIdentityRightLemma2 (x, y) = Refl

stateMonadLawIdentityRightLemma : (f : (s -> (a, s))) -> (x : s) -> (fst (f x), snd (f x)) = f x
stateMonadLawIdentityRightLemma f x = stateMonadLawIdentityRightLemma2 (f x)

stateMonadLawIdentityRight : (n : State s a) -> (n >>>== (\x => stateFunc \state => (x, state))) `equalsTo` n
stateMonadLawIdentityRight (stateFunc f) = stateEq $ funcEqType (\state => (fst (f state), snd (f state)))
                                                                f
                                                                (stateMonadLawIdentityRightLemma f)

stateMonadLawCompositionLemma3 : (z : State s b) -> (y : s)  -> (g : (b -> State s c)) -> getStateFunc (g (fst (getStateFunc z y))) (snd (getStateFunc z y)) = getStateFunc (z >>>== g) y
stateMonadLawCompositionLemma3 (stateFunc f) y g = Refl

stateMonadLawCompositionLemma2 : (result : (a, s)) -> (g : (b -> State s c)) -> (f : (a -> State s b)) -> getStateFunc (g (fst (getStateFunc (f (fst result)) (snd result)))) (snd (getStateFunc (f (fst result)) (snd result))) = getStateFunc (f (fst result) >>>== g) (snd result)
stateMonadLawCompositionLemma2 (x, y) g f = stateMonadLawCompositionLemma3 (f x) y g

stateMonadLawCompositionLemma : (e : (s -> (a, s))) -> (g : (b -> State s c)) -> (f : (a -> State s b)) -> (x : s) -> getStateFunc (g (fst (getStateFunc (f (fst (e x))) (snd (e x))))) (snd (getStateFunc (f (fst (e x))) (snd (e x)))) = getStateFunc (f (fst (e x)) >>>== g) (snd (e x))
stateMonadLawCompositionLemma e g f x = stateMonadLawCompositionLemma2 (e x) g f

stateMonadLawComposition : (n : State s a) -> (f : a -> State s b) -> (g : b -> State s c) ->
                           ((n >>>== f) >>>== g) `equalsTo` (n >>>== \x => f x >>>== g)
stateMonadLawComposition (stateFunc e) f g = stateEq $ funcEqType (getStateFunc $ (stateFunc e >>>== f) >>>== g)
                                                                  (getStateFunc $ stateFunc e >>>== \x => f x >>>== g)
                                                                  (stateMonadLawCompositionLemma e g f)

(s : Type) => MyMonad (State s) where
  myReturn = stateReturn
  (>>>=) = (>>>==)
  monadLawIdentityLeft = stateMonadLawIdentityLeft
  monadLawIdentityRight = stateMonadLawIdentityRight
  monadLawComposition = stateMonadLawComposition
