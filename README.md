The introduction of `ConstraintKinds` in GHC has mainly received attention for making on type of issue easy to solve.

The perhaps most obvious example, as given in [the original blog post on `ConstraintKinds`](http://blog.omega-prime.co.uk/?p=127), is a monad instance for `Set`:

    instance RMonad S.Set where
      type RMonadCtxt S.Set a = Ord a
      return = S.singleton
      mx >>= fxmy = S.fromList [y | x <- S.toList mx, y <- S.toList (fxmy x)]

where `RMonad` is the `Monad` class plus an added `Constraint` `RMonadCtxt`, which allows the `Set` instance to constrict `return` and `>>=` to `Ord a => S.Set a` rather than general `forall a. S.Set a`.

This pattern of defining a "constrained version" of some existing type class ad-hoc (with a constrain specifically for types turning up in that class's methods), while applicable, is bound to lead to many incompatible instances. It does not really obey the mathematical concepts from category theory.

With this library we attemp to better things, by actually starting right from the `Category` class. This is not a new idea, and has not intrinsically much to do with `ConstraintKinds`. But it turns out the combination of re-doing the category-theory stuff with focus on `ConstraintKinds` works quite well.

The outset
---

Haskell has, and makes great use of, powerful facilities from category theory – basically various variants of functors.

However, all those are just endofunctors in **Hask**, the category of all Haskell types with functions as morphisms. Which is sufficient for container / control structures that you want to be able to handle any type of data, but otherwise a bit limiting, seeing as there are (in maths, science etc.) many categories that cannot properly be represented this way. Commonly used libraries such as [vector-space](http://hackage.haskell.org/package/vector-space) thus make little use of the fact that the objects they deal with actually form a category. Instead, just specialised versions of the operations are defined.

Haskell sure can do better than that!<br>
[package/categories](http://hackage.haskell.org/package/categories) rolls up the category theory much more rigorously, with all the correct and general notions as would be used in a mathematical treatment. Functors are not limited to any particular category, functions are generalised to closed cartesian category morphisms, and rather than just having a monad type class thown in you get a fine-grained hierarchy and define monoidal endofunctors.<br>
[data-category](http://hackage.haskell.org/package/data-category) is even more elaborate, defining functors themselves as morphisms in the category **Cat**.

While this may be in principle the ideal way to go about this, it is neither simple to learn nor adapt to actual Haskell programs, with their somewhat sloppy but effective-proven notion of functors and monads in particular.

On the other side of the spectrum, there are packages like [ConstraintKinds](http://hackage.haskell.org/package/ConstraintKinds), which focus on just allowing more instances of the functor through monad classes to be defined.
This allows for some practically useful things like the `Monad` instance of the standard `Set` container as discussed above, without introducing much to be learned or changed about existing Haskell programs; but it hardly generalises the classes themselves and certainly does not open up new opportunities for using specific categories in a canonical manner. Moreover, it is not readily clear how exactly these generalised classes relate to the old plain **Hask** endofunctors.

The solution
---


This package attempts to offer a good compromise between the two approaches. Two crucial changes are made, relative to the established standard classes:

- Functors are parameterised on the two categories they map between.
  If both are `(->)`, we have an ordinary **Hask**-endofunctor and all works like what we're used to.
  In fact, this parameterisation allows there to be a safe (non-overlapping) generic instance: all instances `Prelude.Functor f` give rise to `instance Control.Functor.Constrained.Functor f (->) (->)`.
 Likewise for `Applicative` and `Monad`.
 As a result, it is trivial to adapt Haskell code to the classes from this package if you just import the "`Constrained`" modules.
 Any of the numerous monad etc. instances, from any package, can immediately be used as **Hask**-specific instances of the general `Monad` class.

 But functors can as well map between other categories!

- A category is classified by its morphisms. The objects on the other hand remain ordinary types of kind `*`, but with one important constraint, namely `Object`.
 This allows a category to narrow its objects down to e.g. totally ordered types, or vector spaces, or whatever your morphisms and functors require.


Short HowTo
---

First on importing the modules. The classes are designed to have good backwards-compatibility, so you basically don't need the `Prelude` versions at all anymore. Here's the recommended import list:

    import Control.Category.Constrained.Prelude
    import qualified Control.Category.Hask as Hask
    
    import Control.Monad.Constrained

Most of your existing code should still work after this import change. The compiler will silently replace the `Prelude.>>=` operators with `Control.Monad.Constrained.>>=` and so on, which, though the signatures look much more complicated at first glance, are completely equivalent within the `(->)` category.

What will not work is if you

- Write generic `Functor` / `Applicative` / `Monad` routines with explicit signatures. Those classes are now `MultiParamTypeClasses`; if you put them in a constraint you need to add what category you desire; so if it's **Hask** you should write `(Functor f (->) (->), Num n) => ...`.
- Define your own instances for these classes. You might now be tempted to make it
        
        instance Functor YourFunctor (->) (->) where
          fmap = ...

  however, this would give an `OverlappingInstances` clash with the generic instance: any old (or new!) **Hask** endofunctor is automatically a `Functor f (->) (->)`. So the correct way is actually to define

        instance Hask.Functor YourFunctor where
          Hask.fmap = ...

where `Hask.Functor` is just the plain old `Functor` class from the prelude, as re-imported through `Control.Category.Hask`.

As for actually doing stuff you couldn't have also done with `Prelude.Monad` etc. – There are mainly two such things:

#### Constrain a given category to a particular class of objects.

This would again apply to the `Set` example, where you need the objects in a set to be `Ord`.

The `Category` module includes the `ConstrainedCategory` newtype wrapper for this purpose. The functor classes have easy helper functions to facilitate defining instances withing such a constrained class. Look up the [`Set` example](https://github.com/leftaroundabout/constrained-categories/blob/master/examples/Set.hs) to see how to do it.

#### Define categories where the morphisms aren't just Haskell functions but some other type of arrow.
