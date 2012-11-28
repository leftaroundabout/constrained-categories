With the introduction of `ConstraintKinds`, GHC has made it a lot easier to generalise the universal-purpose adaptions of the category-theory-based constructs such as `Functor`, `Applicative`, `Monad`, `Category` and `Arrow` to type constructors that fulfill the requirements for those classes with _some_ types, but not with _any_ type as required by the Prelude definition.

The perhaps most obvious example, as given in [the original blog post on `ConstraintKinds`](http://blog.omega-prime.co.uk/?p=127), is a monad instance for `Set`:

    instance RMonad S.Set where
      type RMonadCtxt S.Set a = Ord a
      return = S.singleton
      mx >>= fxmy = S.fromList [y | x <- S.toList mx, y <- S.toList (fxmy x)]

where `RMonad` is the `Monad` class plus an added `Constraint` `RMonadCtxt`, which allows the `Set` instance to constrict `return` and `>>=` to `Ord a => S.Set a` rather than general `forall a. S.Set a`.

<hr>

The naming scheme employed here tries to avoid clashes with the Prelude as well as the [`rmonad` package](http://hackage.haskell.org/package/rmonad) (which does not use actual constraint kinds yet).

The constrained version of a standard class `Ξ` is named `CΞ`, e.g. the constrained version of `Applicative` is `CApplicative`. Methods and other functions are prefixed with a `c` without uppercasing the first letter of the original name, e.g. `cfmap`. Infix operators are postfixed with a `#`, like in `<*>#`.

The module names are obtained as `Control.Ξ.Constrained`, e.g. `Control.Functor.Contrained`.
