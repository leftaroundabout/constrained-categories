Before browsing [the Hackage documentation](http://hackage.haskell.org/package/constrained-categories) (which looks a bit scary in places), you may want to read this first.

About
---

The introduction of `ConstraintKinds` in GHC has mainly received attention for making one type of issue easy to solve.

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

This package attempts to offer a good compromise between the two approaches. It is very similar to [packages/hask](http://hackage.haskell.org/package/hask-0), but actually keeps even closer to the `base` modules.

Two crucial changes are made, relative to the established standard classes:

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

    import Prelude ()
    
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

If you have an entirely new category,

    data YourCat a b = ...

and want to use it with this library, you need to define a couple of class instances. The classes in this library form a rather fine hierarchy, much finer than the standard `Arrow`; here's a guide you may use to determine which instances to define and which not, for your category:

- [`Category`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Category-Constrained.html#t:Category) corresponds exactly to the homonymous standard class.
  - [`Cartesian`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Category-Constrained.html#t:Cartesian) allows to do “obvious” transformations on tuples, like swapping elements. You probably want this for almost all categories you define.
    - [`Curry`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Category-Constrained.html#t:Curry) does what it says: you can curry and uncurry morphisms. This is actually a pretty strong operation, only possible in [cartesian closed categories](https://en.wikipedia.org/wiki/Cartesian_closed_category). You may want to skip this for the beginning.
    - [`Morphism`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Arrow-Constrained.html#t:Morphism) represents one half of the standard `Arrow` class. This is still almost as basic as `Cartesian`.
      - [`PreArrow`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Arrow-Constrained.html#t:PreArrow) is the other, substantially stronger half. Unlike with `Morphism`, some interesting categories aren't instances of this class, namely all categories which are “information-preserving”, since `PreArrow` allows both duplicating (`&&&`) and “forgetting” (`fst`/`snd`) information. In particular, this class therefore can't contain truely _invertible_ arrows.
        - [`WellPointed`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Arrow-Constrained.html#t:WellPointed) is yet more specific; together with `Curry` it completes _cartesian closedness_.
  - [`CoCartesian`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Category-Constrained.html#t:CoCartesian), like `Cartesian`, expresses obvious isomorphisms, but on sum types (i.e. [`Either`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Category-Constrained.html#t:-43-)) instead of products (tuples). This also includes booleans and `Maybe`, which Haskell traditionally expresses as separate ADTs, though they are basically just specific instantiations of `Either`.
    - [`MorphChoice`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Arrow-Constrained.html#t:MorphChoice) is dual to `Morphism`.
      - [`PreArrChoice`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Arrow-Constrained.html#t:PreArrChoice) is dual to `PreArrow`. A class that's all of `WellPointed`, `PreArrChoice` and `Curry` is [bicartesian closed](http://ncatlab.org/nlab/show/bicartesian+closed+category), an extremely strong property – such categories can essentially do anything you can do in **Hask**, or generally in lambda calculi.
  - [`SPDistribute`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Arrow-Constrained.html#t:SPDistribute) combines the product- and sum-classes in the algebraic sense: it offers the isomorphism _a_ · (_b_ + _c_) = _a_ · _b_ + _a_ · _c_, in Haskell `(a, Either b c) <-> Either (a,b) (a,c)`.
  - [`HasAgent`](http://hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Category-Constrained.html#t:HasAgent), [`CartesianAgent`](hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Arrow-Constrained.html#t:CartesianAgent) and [`PointAgent`](hackage.haskell.org/package/constrained-categories-0.2.0.0/docs/Control-Arrow-Constrained.html#t:PointAgent) have little to do with category theory as such; they just offer a useful little eDSL for defining arrows in general categories in a similar way as you would in **Hask**, by “pretending” the “results” of your computation are **Hask** objects. The idea is similar to the syntactic sugar offered by [arrow notation](https://www.haskell.org/arrows/syntax.html).


Pros & cons
---

This project differs in particular from [Hask](http://hackage.haskell.org/package/hask) in that the constraints are used explicitly in all the generic functions which somehow compose morphisms. That, frankly, makes the signatures of even simple generic operations look awful, because they internally use compositions with tuples and functor-applications. For instance,

    guard :: (MonadPlus m k, Arrow k (->), Function k, UnitObject k ~ (), Object k Bool)
         => Bool `k` m () 
    
    forever :: (Monad m k, Function k, Arrow k (->), Object k a, Object k b, Object k (m a), Object k (m (m a)), ObjectPoint k (m b), Object k (m (m b)))
         => m a `k` m b 

The good thing is that all these constraints can be automatically inferred (and, hopefully, inlined & optimised) by the compiler. For any actual instantiation, you shouldn't need to worry, because these combined constraints are trivially fulfilled if so are the components.

Trying to generalise random existing code to the classes in this package works empirically kind of well (see [this example](https://github.com/leftaroundabout/constrained-categories/blob/master/examples/Hask.hs)), only when writing more generic stuff the compiler will ask for a lot of things along the lines `Could not infer Object k (c (m a, Bool)) from ...`. This can generally be fixed easily, pretty much by pasting the requested constraints in the signature. Obviously though, this isn't altogether nice and scales badly, in terms of code-amount.

In [Hask](http://hackage.haskell.org/package/hask), the `Op` constraint is only required for generating &ldquo;new&rdquo; arrows; the general philosophy seems to be to pack constraints in GADT dictionaries as much a possible. All in all, that is probably the better solution, but off the top it does require more structure (e.g. `observe`) that differs substantially from the standard modules.

So all in all, this project may be seen as a brute-force hack, generalising the traditional base-classes as much as possible without actually changing the interface.
