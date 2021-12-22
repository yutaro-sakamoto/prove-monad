import Interfaces

infixr 7 :::
infixr 7 +++

data MyList : (a : Type) -> Type where
  MyNil : MyList a
  (:::) : a -> MyList a -> MyList a

data ListEq : list1 -> list2 -> Type where
  nilEq : ListEq MyNil MyNil
  consEq : (headEqPrf : x = y) -> (tailEqPrf : ListEq xs ys) -> ListEq (x ::: xs) (y ::: ys)

(+++) : (xlist : MyList a) -> (ylist : MyList a) -> MyList a
(+++) MyNil ylist = ylist
(+++) xlist MyNil = xlist
(+++) (x ::: xs) ylist = x ::: (xs +++ ylist)

listEqReflexive : {xlist : MyList a} -> xlist `ListEq` xlist
listEqReflexive {xlist = MyNil} = nilEq
listEqReflexive {xlist = (x ::: xs)} = consEq Refl listEqReflexive

listEqSymmetry : {xlist, ylist : MyList a} -> xlist `ListEq` ylist -> ylist `ListEq` xlist
listEqSymmetry {xlist = MyNil} {ylist = MyNil} nilEq = nilEq
listEqSymmetry {xlist = MyNil} {ylist = (x ::: y)} xlist_eq_ylist impossible
listEqSymmetry {xlist = (x ::: xs)} {ylist = MyNil} xlist_eq_ylist impossible
listEqSymmetry {xlist = (x ::: xs)} {ylist = (y ::: ys)} (consEq headEqPrf tailEqPrf) =
  consEq (sym headEqPrf) (listEqSymmetry tailEqPrf)

listEqTransitive : {xlist, ylist, zlist : MyList a} -> xlist `ListEq` ylist -> ylist `ListEq` zlist -> xlist `ListEq` zlist
listEqTransitive {xlist = MyNil} {ylist = MyNil} {zlist = MyNil} nilEq ylist_eq_zlist = ylist_eq_zlist
listEqTransitive {xlist = MyNil} {ylist = MyNil} {zlist = (x ::: y)} nilEq ylist_eq_zlist impossible
listEqTransitive {xlist = (x:::xs)} {ylist = (y:::ys)} {zlist = MyNil} (consEq headEqPrf tailEqPrf) ylist_eq_zlist impossible 
listEqTransitive {xlist = (x:::xs)} {ylist = (y:::ys)} {zlist = (z:::zs)} (consEq x_eq_y xs_eq_ys) (consEq y_eq_z ys_eq_zs) =
  consEq (rewrite x_eq_y in y_eq_z) (listEqTransitive xs_eq_ys ys_eq_zs)

mapList : (f : a -> b) -> (xs : MyList a) -> MyList b
mapList f MyNil = MyNil
mapList f (x ::: xs) = f x ::: mapList f xs

listFunctorLawIdentity : (xlist : MyList a) -> mapList Prelude.id xlist `ListEq` xlist
listFunctorLawIdentity MyNil = nilEq
listFunctorLawIdentity (x ::: xs) = consEq Refl (listFunctorLawIdentity xs)

listFunctorLawComposition : (v : b -> c) -> (u : a -> b) -> (xlist : MyList a) -> mapList (v . u) xlist `ListEq` mapList v (mapList u xlist)
listFunctorLawComposition v u MyNil = nilEq
listFunctorLawComposition v u (x ::: xs) = consEq Refl (listFunctorLawComposition v u xs)

MyFunctor MyList where
  equalsTo = ListEq
  eqReflexive = listEqReflexive
  eqSymmetry = listEqSymmetry
  eqTransitive = listEqTransitive
  myMap = mapList
  functorLawIdentity = listFunctorLawIdentity
  functorLawComposition = listFunctorLawComposition

returnList : a -> MyList a
returnList x = x ::: MyNil

infixl 1 >>>==

(>>>==) : (xlist : MyList a) -> (f : a -> MyList b) -> MyList b
MyNil >>>== f = MyNil
(x ::: xs) >>>== f = f x +++ (xs >>>== f)

listMonadLawIdentityLeftLemma : (z : MyList b) -> ListEq (z +++ MyNil) z
listMonadLawIdentityLeftLemma MyNil = nilEq
listMonadLawIdentityLeftLemma (z ::: zs) = consEq Refl listEqReflexive

listMonadLawIdentityLeft : (x : a) -> (f : a -> MyList b) -> (returnList x >>>== f) `ListEq` (f x)
listMonadLawIdentityLeft x f = listMonadLawIdentityLeftLemma (f x)

listTwoEqLemma : (z : a) -> (xlist : MyList a) -> (ylist : MyList a) -> (xlist_eq_ylist : ListEq xlist ylist) -> ListEq ((z ::: MyNil) +++ ylist) (z ::: xlist)
listTwoEqLemma z MyNil MyNil nilEq = consEq Refl nilEq
listTwoEqLemma _ MyNil (_ ::: _) nilEq impossible
listTwoEqLemma _ MyNil (_ ::: _) (consEq headEqPrf tailEqPrf) impossible
listTwoEqLemma _ (_ ::: _) MyNil nilEq impossible
listTwoEqLemma _ (_ ::: _) MyNil (consEq headEqPrf tailEqPrf) impossible
listTwoEqLemma z (x ::: xs) (y ::: ys) (consEq headEqPrf tailEqPrf) = consEq Refl (consEq (sym headEqPrf) (listEqSymmetry tailEqPrf))

listMonadLawIdentityRight : (n : MyList a) -> (n >>>== (::: MyNil)) `ListEq` n
listMonadLawIdentityRight MyNil = nilEq
listMonadLawIdentityRight (x ::: xs) = listTwoEqLemma x xs (xs >>>== (::: MyNil)) (listEqSymmetry $ listMonadLawIdentityRight xs)

listAppendNilLemma : (xlist : MyList a) -> xlist `ListEq` (xlist +++ MyNil)
listAppendNilLemma MyNil = nilEq
listAppendNilLemma (x ::: xs) = listEqReflexive

replaceLeft : (xlist : MyList a) -> (ylist : MyList a) -> (zlist : MyList a) -> (xlist_eq_ylist : ListEq xlist ylist) ->
              ListEq (xlist +++ zlist) (ylist +++ zlist)
replaceLeft MyNil MyNil MyNil nilEq = nilEq
replaceLeft MyNil MyNil (z ::: zs) nilEq = listEqReflexive
replaceLeft MyNil (_ ::: _) MyNil nilEq impossible
replaceLeft MyNil (_ ::: _) MyNil (consEq headEqPrf tailEqPrf) impossible
replaceLeft MyNil (_ ::: _) (_ ::: _) nilEq impossible
replaceLeft MyNil (_ ::: _) (_ ::: _) (consEq headEqPrf tailEqPrf) impossible
replaceLeft (_ ::: _) MyNil MyNil nilEq impossible
replaceLeft (_ ::: _) MyNil MyNil (consEq headEqPrf tailEqPrf) impossible
replaceLeft (_ ::: _) MyNil (_ ::: _) nilEq impossible
replaceLeft (_ ::: _) MyNil (_ ::: _) (consEq headEqPrf tailEqPrf) impossible
replaceLeft (x ::: xs) (y ::: ys) MyNil (consEq headEqPrf tailEqPrf) = consEq headEqPrf tailEqPrf
replaceLeft (x ::: xs) (y ::: ys) (z ::: zs) (consEq headEqPrf tailEqPrf) = consEq headEqPrf (replaceLeft xs ys (z ::: zs) tailEqPrf)

replaceRight : (xlist : MyList a) -> (ylist : MyList a) -> (zlist : MyList a) -> (xlist_eq_ylist : ListEq ylist zlist) ->
              ListEq (xlist +++ ylist) (xlist +++ zlist)
replaceRight MyNil MyNil MyNil nilEq = nilEq
replaceRight MyNil MyNil (_ ::: _) nilEq impossible
replaceRight MyNil MyNil (_ ::: _) (consEq headEqPrf tailEqPrf) impossible
replaceRight MyNil (_ ::: _) MyNil nilEq impossible
replaceRight MyNil (_ ::: _) MyNil (consEq headEqPrf tailEqPrf) impossible
replaceRight MyNil (y ::: ys) (z ::: zs) (consEq headEqPrf tailEqPrf) = consEq headEqPrf tailEqPrf
replaceRight (x ::: xs) MyNil MyNil nilEq = listEqReflexive
replaceRight (_ ::: _) MyNil (_ ::: _) nilEq impossible
replaceRight (_ ::: _) MyNil (_ ::: _) (consEq headEqPrf tailEqPrf) impossible
replaceRight (_ ::: _) (_ ::: _) MyNil nilEq impossible
replaceRight (_ ::: _) (_ ::: _) MyNil (consEq headEqPrf tailEqPrf) impossible
replaceRight (x ::: xs) (y ::: ys) (z ::: zs) (consEq headEqPrf tailEqPrf) = consEq Refl (replaceRight xs (y ::: ys) (z ::: zs) (consEq headEqPrf tailEqPrf))

replaceBoth : (xlist : MyList a) -> (ylist : MyList a) -> (zlist : MyList a) -> (wlist : MyList a) -> (xlist_eq_zlist : ListEq xlist zlist) -> (ylist_eq_wlist : ListEq ylist wlist) ->
              ListEq (xlist +++ ylist) (zlist +++ wlist)
replaceBoth xlist ylist zlist wlist xlist_eq_zlist ylist_eq_wlist =
  (listEqReflexive `listEqTransitive` replaceLeft xlist zlist ylist xlist_eq_zlist) `listEqTransitive` replaceRight zlist ylist wlist ylist_eq_wlist

concatAssociative : (xlist : MyList a) -> (ylist : MyList a) -> (zlist : MyList a) ->
                    ListEq (xlist +++ ylist +++ zlist) ((xlist +++ ylist) +++ zlist)
concatAssociative MyNil MyNil MyNil = nilEq
concatAssociative MyNil MyNil (z ::: zs) = listEqReflexive
concatAssociative MyNil (y ::: ys) MyNil = listEqReflexive
concatAssociative MyNil (y ::: ys) (z ::: zs) = listEqReflexive
concatAssociative (x ::: xs) MyNil MyNil = listEqReflexive
concatAssociative (x ::: xs) MyNil (z ::: zs) = listEqReflexive
concatAssociative (x ::: xs) (y ::: ys) MyNil = listEqReflexive
concatAssociative (x ::: xs) (y ::: ys) (z ::: zs) = consEq Refl (concatAssociative xs (y ::: ys) (z ::: zs))

distributiveLaw : (z : a) -> (zs : MyList a) -> (x : a) -> (xs : MyList a) -> (g : a -> MyList b) ->
                           (induction_assumption : ListEq ((zs +++ (x ::: xs)) >>>== g) ((zs >>>== g) +++ ((x ::: xs) >>>== g))) ->
                           ListEq (g z +++ ((zs +++ (x ::: xs)) >>>== g)) (g z +++ (zs >>>== g) +++ ((x ::: xs) >>>== g))
distributiveLaw z zs x xs g induction_assumption =
  replaceRight (g z) ((zs +++ (x ::: xs)) >>>== g) ((zs >>>== g) +++ ((x ::: xs) >>>== g)) induction_assumption

--(((z ::: zs) +++ (x ::: xs)) >>>== g) -- distribute1
--(g z +++ ((zs +++ (x ::: xs)) >>>== g)) -- distributeIndctionLemma
--(g z +++ (zs >>>== g) +++ ((x ::: xs) >>>== g)) -- distribute 2
--(g z +++ (zs >>>== g) +++ g x +++ (xs >>>== g)) -- assosiativeLemma
--((g z +++ (zs >>>== g)) +++ (g x +++ (xs >>>== g))) -- distribute 3
--((z ::: zs) >>>== g) +++ ((x ::: xs) >>>== g)

listMonadLawCompositionLemma : (zlist : MyList a) -> (xlist : MyList a) -> (g : a -> MyList b) ->
                               ListEq ((zlist +++ xlist) >>>== g) ((zlist >>>== g) +++ (xlist >>>== g))
listMonadLawCompositionLemma MyNil MyNil g = nilEq
listMonadLawCompositionLemma MyNil (x ::: xs) g = listEqReflexive
listMonadLawCompositionLemma (z ::: zs) MyNil g = listAppendNilLemma (g z +++ (zs >>>== g))
listMonadLawCompositionLemma (z ::: zs) (x ::: xs) g =
  distributiveLaw z zs x xs g (listMonadLawCompositionLemma zs (x ::: xs) g) `listEqTransitive`
  concatAssociative (g z) (zs >>>== g) (g x  +++ (xs >>>== g))

--((x ::: xs) >>>== f) >>>== g
--(f x +++ (xs >>>== f)) >>>== g
--((f x) >>>== g) +++ ((xs >>>== f) >>>== g)
--((f x) >>>== g) +++ (xs >>>== \z => f z >>>== g)
--((x ::: MyNil) >>>== \z -> f z >>>== g) +++ (xs >>>== \z => f z >>>== g)
--((x ::: MyNil) +++ xs) >>>== \z => f z >>>= g
--(x ::: xs) >>>== \z => fz >>>= g

listMonadLawComposition : (xlist : MyList a) -> (f : a -> MyList b) -> (g : b -> MyList c) ->
                          ((xlist >>>== f) >>>== g) `ListEq` (xlist >>>== \z => f z >>>== g)
listMonadLawComposition MyNil f g = nilEq
listMonadLawComposition (x ::: xs) f g = 
  (listMonadLawCompositionLemma (f x) (xs >>>== f) g `listEqTransitive`
  replaceRight (f x >>>== g) ((xs >>>== f) >>>== g) (xs >>>== (\z => f z >>>== g)) (listMonadLawComposition xs f g)) `listEqTransitive`
  listEqReflexive

MyMonad MyList where
  myReturn = returnList
  (>>>=) = (>>>==)
  monadLawIdentityLeft = listMonadLawIdentityLeft
  monadLawIdentityRight = listMonadLawIdentityRight
  monadLawComposition = listMonadLawComposition
