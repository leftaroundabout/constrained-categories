With the introduction of `ConstraintKinds`, GHC has made it a lot easier to generalise the universal-purpose adaptions of the category-theory-based constructs such as `Functor`, `Applicative`, `Monad`, `Category` and `Arrow` to type constructors that fulfill the requirements for those classes with _some_ types, but not with _any_ type as required by the Prelude definition.

The perhaps most obvious example, as given in [the original blog post on `ConstraintKinds`](http://blog.omega-prime.co.uk/?p=127), is a monad instance for `Set`:

    instance RMonad S.Set where
      type RMonadCtxt S.Set a = Ord a
      return = S.singleton
      mx >>= fxmy = S.fromList [y | x <- S.toList mx, y <- S.toList (fxmy x)]

where `RMonad` is the `Monad` class plus an added `Constraint` `RMonadCtxt`, which allows the `Set` instance to constrict `return` and `>>=` to `Ord a => S.Set a` rather than general `forall a. S.Set a`.

<hr>

This pattern of defining a "constrained version" of some existing type class ad-hoc (with a constrain specifically for types turning up in that class's methods), while applicable, is bound to lead to many incompatible instances, it does not really obey the mathematical concepts from category theory.

This library attemps to better things, by actually starting right from the `Category` class. The flip side is that the resulting classes can't be expected to permit instances for already-existing types as readily as specific versions do.



