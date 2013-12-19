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

The outset
---

Haskell has, and makes great use of, powerful facilities from category
theory – basically various variants of functors.

However, all those are just endofunctors in Hask, the category of
all Haskell types with functions as morphisms. Which is sufficient
for container / control structures that you want to be able to handle 
any type of data, but otherwise a bit limiting, seeing as 
there are (in maths, science etc.) many categories that cannot properly
be represented this way. Commonly used libraries such as 
[vector-space](http://hackage.haskell.org/package/vector-space) thus make 
little notion of the fact that the objects they deal with actually
form a category, instead defining just specialised versions of
the operations.

Haskell sure can do better than that!
<http://hackage.haskell.org/package/categories> rolls up the category
theory much more rigorously, with all the correct and general notions
as would be used in a mathematical treatment. Functors are not limited
to any particular category, functions are generalised to closed
cartesian category morphisms, and rather than just having a monad
type class thown in you get a fine-grained hierarchy and define
monoidal endofunctors.
[data-category](http://hackage.haskell.org/package/data-category) is even more
elaborate, defining functors themselves as morphisms in the category
Cat.

While this may be in principle the ideal way to go about this,
it is neither simple to learn nor adapt to actual Haskell programs,
with their somewhat sloppy but effective-proven notion of functors
and monads in particular.

On the other side of the spectrum, there are packages like
[ConstraintKinds](http://hackage.haskell.org/package/ConstraintKinds), which focus
on just allowing more instances of the functor through monad classes
to be defined. This allows for some practically useful things like
the `Monad` instance of the standard `Set` container as discussed above, without introducing
much to be learned or changed about existing Haskell programs;
but it hardly generalises
the classes themselves and certainly does not open up new opportunities
for using specific categories in a canonical manner. Moreover, it
is not readily clear how exactly these generalised classes relate
to the old plain Hask endofunctors.

The Solution
===

This package attempts to offer a good compromise between the two
approaches. Two crucial changes are made, relative to the established
standard classes:

- Functors are parameterised on the two categories they map between.
If both are `(->)`, we have an ordinary Hask-endofunctor and all
works like what we're used to. In fact, this parameterisation allows
there to be a safe (non-overlapping) generic instance: all instances
`Prelude.Functor f` give rise to
`instance Control.Functor.Constrained.Functor f (->) (->)`. Likewise
for `Applicative`
and `Monad`. As a result, it is trivial
to adapt Haskell code to the classes from this package if you
just import the "`Constrained`" modules. Any of the numerous
monad etc. instances, from any package, can immediately be used
as Hask-specific instances of the general `Monad` class.

 But functors can as well map between other categories!

- A category is classified by its morphisms. The objects on the other
hand remain ordinary types of kind `*`, but with one important
constraint, namely `Object`. This
allows a category to narrow its objects down to e.g. totally
ordered types, or vector spaces, or whatever your morphisms and
functors require.
