---
title: "Categories and the art of compilation"
author: "Ajinkya Kulkarni"
---
$\require{AMScd}
\require{xymatrix}
\require{amsmath}
\require{amssymb}
\require{xcolor}$

[tobias]: desperatly_need_running_example

[test_tobias]: this is a single comment, right?

# Categories and the art of compilation

Anoma's [Juvix](https://juvix.org/) aims to compile to zk-circuits written in a functional programming, making it easy to generate arithmetic circuits, e.g., in [Vamp-IR](https://github.com/anoma/vamp-ir). Moreover, Vamp-IR yields intermediate representation for multivariate polynomials that subsequently can be hooked up to _any_ prover backend, such as [Plonk](https://github.com/fluidex/awesome-plonk) or [Halo2](https://halo2.dev/).

Arithmetic circuits or polynomials are relatively  simple to define in terms of elementary arithmetic operations, and it is indeed an interesting question as to how one may express programs written in a full-fledged functional programming language in terms of these elementary operations. In this post, we address how we have solved this problem by developing a  programming language called [GEB](https://github.com/anoma/geb). GEB provides us with a way to define verifiable compilers, one which compiles to arithmetic circuits. The ability to verify compilers allows us to easily deploy and update distributed and cryptographic systems without jeopardizing their security and robustness. Further, it also allows anyone to contribute to the compiler code, as long as they can produce a proof that it satisfies certain properties.

Compilers have traditionally been organized broadly in terms of a front-end which handles syntax and semantics and a backend which generates code in the target language. From a formal standpoint, this approach has been "ad-hoc" in the following sense: the big body of research about compiler correctnes in fact comes to the conclusion that we need a universal approach for compiler correctness. For example, a compiler that verifies correctness for one language, say C, does not know how to verify the correctness of a program written in Rust, although the underlying concepts for verification remain the same. This leads to unnecessary duplication of efforts, when one could  have abstracted the process of verification and applied it to various semantic models (say C, Rust or any other language). There are existing tools that achieve this to a certain extent, but our approach distinguishes itself by using category theory.

<!-- 
[comment_tobias]:  above pragraph can go?
-->

[Category theory](https://en.wikipedia.org/wiki/Category_theory) turns out to be the right framework in which to think about (and solve) the problem of a universal approach to verifying correctness. Compilation has long been described as the "translation" of one language to another, via a series of transformations (or passes) which themselves may be understood as translations of intermediate representations (which are  languages in their own right) that emerge during the process of compilation. Given the languages under consideration, we view each language as a [category](https://en.wikipedia.org/wiki/Category_(mathematics)#Definition), with its types as objects and the functions between two types constituting the space of morphisms (or the Hom space in categorical lingo). A compiler pass then becomes a the application of a [functor](https://en.wikipedia.org/wiki/Functor#Definition) from the source to the target language, satisfying certain properties.

At first glance, this picture may seem a little tacked-on, but it provides a mathematically rigorous foundation not only for the compilation process in general, but for every compiler pass. It is possible to reason about properties of the functor associated with each compiler pass, and studying [natural transformations](https://en.wikipedia.org/wiki/Natural_transformation#Definition) between two functors allow us to rigorously compare two separate approaches to implementing a pass with the same source and target languages.

Since category theory lays great emphasis on [universal constructions](https://ncatlab.org/nlab/show/universal+construction), it is able to define many things in the most general manner possible. For example, every functional programming language has its own way of implementing the lambda calculus, but there is only one way to define a category that supports lambda expressions, which is done by defining the [exponential object](https://en.wikipedia.org/wiki/Exponential_object) and the attendant $eval$ and $curry$ morphisms. Verifying a property amounts to determining a well-defined functor from a categorical model of any implementation language to the GEB core category.

We harness the power of category theory to define our language GEB, which is category-theoretically unique minimal Lisp. In particular, GEB allows us to define a category, $\tt FinPoly$, that  models polynomials—provably correct. The key feature of this category is that it supports lambda expressions, higher-order functions, polymorphism and even dependent types. GEB also allows us to write compilers to and from $\tt FinPoly$. To wit, any reasonable functional programming language can compile to this category. 

The category $\tt FinPoly$ is defined as the category of [polynomial endofunctors](https://ncatlab.org/nlab/show/polynomial+functor) of $\tt PFS$, the programmer's finite set category, which is a [bicartesian closed category](https://en.wikipedia.org/wiki/Cartesian_closed_category#Bicartesian_closed_categories). In fact, $\tt PFS$ is the initial object in the category of bicartesian closed categories. We use $\tt PFS$ rather than something more familiar like $\tt Set$ (which is also distributive Bicartesian closed) since we want to avoid non-computable entities, such as uncountable infinities, let alone functions over these. In $\tt PFS$, polynomial endofunctors are finite [products](https://en.wikipedia.org/wiki/Product_(category_theory)) and [coproducts](https://en.wikipedia.org/wiki/Coproduct) of representable functors. Types arise from the iterative application of polynomial endofunctors to the [terminal object](https://en.wikipedia.org/wiki/Initial_and_terminal_objects) of $\tt PFS$. This provides the significant advantage of trivializing termination-checking in GEB. Since all types are inductively defined,  every program written in GEB terminates by definition.

Another important advantage that the categorical approach to compilation provides is a rigorous approach to optimization. Suppose we have a compiler $\bf C$ which compiles $\tt FinPoly$ to $\tt VampIR$, which is the Vamp-IR category.

$$ \tt FinPoly \xrightarrow{\bf C} \tt VampIR$$

Say we make contact with aliens who claim they have a better compiler, i.e. they have categories $\tt OptFinPoly$, $\tt OptVampIR$ and a functor $\bf C'$ between them, which are optimizations of $\tt FinPoly$, $\tt VampIR$ and $\bf C$, respectively.  With our ongoing research, we hope to be able to verify the aliens' claims, by checking the commutativity of the following naturality square in the category of bicartesian closed categories.

$$
\begin{CD}
\tt FinPoly @>{\bf C}>> \tt VampIR\\
@VVV @VVV \\
\tt OptFinPoly @>{\bf C'}>>\tt OptVampIR
\end{CD}$$

Similarly, suppose there is a different compiler $\bf D$. 
$$ \tt FinPoly \xrightarrow{\bf D} \tt VampIR$$

Assuming we have a proof that the compiler $\bf C$ is correct, we would only have to show that there is a natural isomorphism between the functors $\bf C$ and $\bf D$ in order to verify that $\bf D$ is also correct. As this example shows, not only does category theory allow us to formulate the correctness of optimization as a mathematically rigorous problem, it allows us to use already existing proofs to simplify new ones.

In the context of zk-circuits, GEB can compile a program in a functional programming language to a logic-preserving Vamp-IR program. We highlight that we achieve this without the use of a virtual machine (for example, [RISC0](https://www.risczero.com/) or others used in the [ZKP compiler shootout](https://github.com/anoma/zkp-compiler-shootout)).

Take the following example, where we would like to prove that we know a (non-unique) list of pairs of points on the 2d-plane.  The [Euclidean distances](https://en.wikipedia.org/wiki/Euclidean_distance) between each pair constitute the proof. We first define our custom datatype `Point`, which, with its eponymous constructor, constructs a `Point` from a pair of `Int`s.
```haskell!
data Point = Point Int Int
```

We then define the function `distance`, which uses pattern matching and gives us the Euclidean distance between a pair of points. Note that since we are compiling to Vamp-IR, using types like `Float` would give a compile-time error. For this example, we will suppose that we have pairs of integral points whose Euclidean distances are also integral.

```haskell!
distance :: Point -> Point -> Int
distance (Point w x) (Point y z) =  sqrt $ (z - x)^2 + (y - w)^2
```
Now, we use `distance` to compute the required distances. We map the lambda expression $\lambda x. distance\; x$, over our list of pairs of points, with $x=$`(a, b)`, where `a` and `b` are `Point`s. The program is expressed in the [point-free style](https://en.wikipedia.org/wiki/Tacit_programming).

```haskell!
distanceBetween :: [(Point, Point)] -> [Int]
distanceBetween = map (\(a, b) -> distance a b)
```

The complete program now looks like this.
```haskell!
data Point = Point Int Int

distance :: Point -> Point -> Int
distance (Point w x) (Point y z) =  sqrt $ (z - x)^2 + (y - w)^2

distanceBetween :: [(Point, Point)] -> [Int]
distanceBetween = map (\(a, b) -> distance a b) 
```


The above program would compile to VampIR via GEB, without the need for a virtual machine. The complete VampIR program now looks like this.

```!
def square_root m {
  def y = x * x;
  m = y;
  x
}

def distance w x y z {
square_root ((z -x)^2 + (y-w)^2) 
}

map distance pts
```

We first have the `square_root` function. It takes an input `m` and defines a constraint equation $y=x^2$ for $y=$`m`, and solves for $x$. As mentioned earlier, Vamp-IR only supports integer types, so this function does not work unless `m` is a perfect square.

The function `distance` corresponds directly to `distance` in our earlier program. Finally, we map this function over the list of points that the prover supplies using `map` in Vamp-IR. The variable `pts` is a free variable, which in Vamp-IR is treated as prover input.

This article only provides a glimpse of our approach to compiling programs (and zk-circuits in particular), which to the best of our knowledge, has not been done before. We undoubtedly stand on the shoulders of giants, the many mathematicians whose efforts led to a solid understanding of the underlying theory. In turn, in putting this theory into practice, we endeavor to make the process of software engineering itself able to stand on the shoulders of giants, by minimizing effort duplication, for instance, via making implementation and property-verification agnostic to the choice of language or via using already existing proofs to simplify new ones with the help of natural transformations.

We have eschewed technical details for a sweeping overview of our approach and its motivations, but follow-up blog posts will shed more light on the mathematics underlying GEB and provide in-depth tutorials on how GEB may be used to a programmer's advantage.

### References

1. The [GEB](https://github.com/anoma/geb) repository (WIP), which also contains [examples](https://github.com/anoma/geb/blob/main/geb/EXAMPLES.md)
1. The [Vamp-IR](https://github.com/anoma/vamp-ir/) respository (WIP)
1. Ideas about compiling to polynomials are described in Conal Elliott's paper, [_Compiling to Categories_](http://conal.net/papers/compiling-to-categories/)
