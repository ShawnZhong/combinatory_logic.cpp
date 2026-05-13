// Pure-TMP deep embedding of the Calculus of Constructions.
//
// Terms are types; β-reduction is a type-level metafunction.  Variables are
// de Bruijn indices, so α-equivalence collapses to is_same and we never need
// fresh-name generation.  This file deliberately crosses the wall in
// concept.cpp: with reduction expressed as metafunctions over our own AST,
// we can β-reduce under opaque variables -- which the host C++ type system
// will not do for templates parameterised by an opaque NTTP.
//
// CoC is presented as a Pure Type System with sorts {*, □}, axiom * : □,
// and rules {(*,*), (*,□), (□,*), (□,□)}.

#include <type_traits>

// =============================================================================
// (A) AST: terms-as-types.
// =============================================================================
struct Star {};                                   // *
struct Box  {};                                   // □  (* : □)
template <int N>                  struct Var {};  // de Bruijn index
template <typename A, typename B> struct Lam {};  // λ:A. B   (annotation, body)
template <typename A, typename B> struct Pi  {};  // Π:A. B   (domain, codomain)
template <typename F, typename X> struct App {};  // F X

// =============================================================================
// (B) lift<T, D, C> : add D to every free variable of T whose index is ≥ C.
//     Used when we splice T under D additional binders.
// =============================================================================
template <typename T, int D, int C = 0> struct lift_ { using type = T; };
template <typename T, int D, int C = 0> using lift = typename lift_<T, D, C>::type;

template <int N, int D, int C> struct lift_<Var<N>, D, C> {
  using type = Var<N + D * (N >= C)>;
};
template <typename A, typename B, int D, int C> struct lift_<Lam<A, B>, D, C> {
  using type = Lam<lift<A, D, C>, lift<B, D, C + 1>>;
};
template <typename A, typename B, int D, int C> struct lift_<Pi<A, B>, D, C> {
  using type = Pi<lift<A, D, C>, lift<B, D, C + 1>>;
};
template <typename F, typename X, int D, int C> struct lift_<App<F, X>, D, C> {
  using type = App<lift<F, D, C>, lift<X, D, C>>;
};

// =============================================================================
// (C) subst<T, N, S> : in T, replace Var<N> with S, decrement free vars > N,
//     and lift S by one each time we descend under a binder.
//     β-rule: (Lam A B) X  →  subst<B, 0, X>.
// =============================================================================
template <typename T, int N, typename S> struct subst_ { using type = T; };
template <typename T, int N, typename S> using subst = typename subst_<T, N, S>::type;

template <int K, int N, typename S> struct subst_<Var<K>, N, S> {
  using type = std::conditional_t<(K == N), S, Var<K - (K > N)>>;
};
template <typename A, typename B, int N, typename S> struct subst_<Lam<A, B>, N, S> {
  using type = Lam<subst<A, N, S>, subst<B, N + 1, lift<S, 1>>>;
};
template <typename A, typename B, int N, typename S> struct subst_<Pi<A, B>, N, S> {
  using type = Pi<subst<A, N, S>, subst<B, N + 1, lift<S, 1>>>;
};
template <typename F, typename X, int N, typename S> struct subst_<App<F, X>, N, S> {
  using type = App<subst<F, N, S>, subst<X, N, S>>;
};

// =============================================================================
// (D) β-reduction.
//     whnf : reduce only redexes at the head.
//     nf   : full normal form -- whnf, then traverse subterms.
//     equiv: is_same on normal forms (β-equivalence; we skip η for now).
// =============================================================================
template <typename T> struct whnf_ { using type = T; };
template <typename T> using whnf = typename whnf_<T>::type;

// App: reduce the head; if it's a Lam, β-reduce, else leave the App neutral.
template <typename F, typename X> struct whnf_<App<F, X>> {
private:
  template <typename Fn> struct go { using type = App<Fn, X>; };
  template <typename A, typename B> struct go<Lam<A, B>> {
    using type = whnf<subst<B, 0, X>>;
  };
public:
  using type = typename go<whnf<F>>::type;
};

template <typename T> struct nf_traverse_ { using type = T; };
template <typename T> using nf_traverse = typename nf_traverse_<T>::type;
template <typename T> using nf = nf_traverse<whnf<T>>;

template <typename A, typename B> struct nf_traverse_<Lam<A, B>> {
  using type = Lam<nf<A>, nf<B>>;
};
template <typename A, typename B> struct nf_traverse_<Pi<A, B>> {
  using type = Pi<nf<A>, nf<B>>;
};
template <typename F, typename X> struct nf_traverse_<App<F, X>> {
  using type = App<nf<F>, nf<X>>;
};

template <typename A, typename B>
inline constexpr bool equiv = std::is_same_v<nf<A>, nf<B>>;

// =============================================================================
// (E) Context as a variadic type pack (innermost first).  Var-lookup is
//     pack-indexed inline in infer_<Var<N>> below.
// =============================================================================
template <typename... Ts> struct Ctx {};

template <typename T, typename C> struct cons_;
template <typename T, typename... Ts> struct cons_<T, Ctx<Ts...>> {
  using type = Ctx<T, Ts...>;
};
template <typename T, typename C> using cons = typename cons_<T, C>::type;

// =============================================================================
// (F) Bidirectional infer.  App enforces argument-type equivalence via
//     static_assert; sort/well-formedness checks elided to keep the kernel
//     tight (callers verify by inspecting the inferred type).
// =============================================================================
template <typename Ctx, typename T> struct infer_;
template <typename Ctx, typename T> using infer = typename infer_<Ctx, T>::type;

template <typename Ctx> struct infer_<Ctx, Star> { using type = Box; };

template <typename... Ts, int N> struct infer_<Ctx<Ts...>, Var<N>> {
  using type = lift<Ts...[N], N + 1>;
};

// Π's sort is the codomain's sort; we just synthesise it.
template <typename Ctx, typename A, typename B> struct infer_<Ctx, Pi<A, B>> {
  using type = infer<cons<A, Ctx>, B>;
};

// λ:A. B  has type  Π:A. (type of B in extended Γ)
template <typename Ctx, typename A, typename B> struct infer_<Ctx, Lam<A, B>> {
  using type = Pi<A, infer<cons<A, Ctx>, B>>;
};

// (F X) requires F : Π:A. T and X : A; result is T[X/0].
template <typename Ctx, typename F, typename X> struct infer_<Ctx, App<F, X>> {
private:
  template <typename FT> struct app_;
  template <typename A, typename T> struct app_<Pi<A, T>> {
    static_assert(equiv<A, infer<Ctx, X>>, "App: argument type mismatch");
    using type = subst<T, 0, X>;
  };
public:
  using type = typename app_<whnf<infer<Ctx, F>>>::type;
};

// =============================================================================
// (G) Sanity: lift / subst on small terms.
// =============================================================================
static_assert(std::is_same_v<lift<Var<0>, 1>, Var<1>>);
static_assert(std::is_same_v<lift<Var<3>, 2, 0>, Var<5>>);
static_assert(std::is_same_v<lift<Var<0>, 9, 1>, Var<0>>);   // below cutoff
static_assert(std::is_same_v<subst<Var<0>, 0, Star>, Star>);
static_assert(std::is_same_v<subst<Var<2>, 0, Star>, Var<1>>);
static_assert(std::is_same_v<subst<App<Var<0>, Var<2>>, 0, Star>,
                             App<Star, Var<1>>>);

// =============================================================================
// (H) Identity, polymorphic in CoC: id := λA:*. λx:A. x  has type ΠA:*. A → A.
// =============================================================================
using Id = Lam<Star, Lam<Var<0>, Var<0>>>;
using IdT = Pi<Star, Pi<Var<0>, Var<1>>>;
static_assert(std::is_same_v<infer<Ctx<>,Id>, IdT>, "id : ΠA:*. A → A");

// β under opaque variables: in any context where Var<1> : * and Var<0> : Var<1>,
// (id Var<1>) Var<0>  reduces to Var<0> -- precisely the move concept.cpp
// could not do symbolically.
using IdAppOpaque = App<App<Id, Var<1>>, Var<0>>;
static_assert(equiv<IdAppOpaque, Var<0>>,
              "(id T) x ≡ x  for opaque T, x");

// =============================================================================
// (I) Church Nat = ΠA:*. (A → A) → A → A
// =============================================================================
using Nat = Pi<Star, Pi<Pi<Var<0>, Var<1>>, Pi<Var<1>, Var<2>>>>;

// zero := λA:*. λf:(A→A). λx:A. x
using Z = Lam<Star, Lam<Pi<Var<0>, Var<1>>, Lam<Var<1>, Var<0>>>>;
static_assert(std::is_same_v<infer<Ctx<>,Z>, Nat>, "zero : Nat");

// succ := λn:Nat. λA:*. λf:(A→A). λx:A. f (n A f x)
using S = Lam<Nat,
            Lam<Star,
              Lam<Pi<Var<0>, Var<1>>,
                Lam<Var<1>,
                  App<Var<1>,
                    App<App<App<Var<3>, Var<2>>, Var<1>>, Var<0>>>>>>>;
static_assert(std::is_same_v<infer<Ctx<>,S>, Pi<Nat, Nat>>, "succ : Nat → Nat");

using One = App<S, Z>;
using Two = App<S, One>;
static_assert(std::is_same_v<infer<Ctx<>,One>, Nat>);
static_assert(std::is_same_v<infer<Ctx<>,Two>, Nat>);

// succ (succ zero) β-reduces to its Church-2 literal.
using ChurchOne = Lam<Star, Lam<Pi<Var<0>, Var<1>>,
                    Lam<Var<1>, App<Var<1>, Var<0>>>>>;
using ChurchTwo = Lam<Star, Lam<Pi<Var<0>, Var<1>>,
                    Lam<Var<1>, App<Var<1>, App<Var<1>, Var<0>>>>>>;
static_assert(equiv<One, ChurchOne>, "succ zero ≡ Church 1");
static_assert(equiv<Two, ChurchTwo>, "succ (succ zero) ≡ Church 2");

// =============================================================================
// (J) The headline gap concept.cpp could not cross.
//
//     Apply Church-2 to three FREE variables T (a type), f : T→T, x : T.
//     Pure β-reduction under three opaque parameters yields f (f x).
//     concept.cpp could verify this only at concrete witnesses; here we
//     reduce symbolically because the redex / substitution lives in our
//     own metafunctions, not in C++'s type-equivalence judgement.
// =============================================================================
using TwoAppOpaque = App<App<App<Two, Var<2>>, Var<1>>, Var<0>>;
static_assert(equiv<TwoAppOpaque, App<Var<1>, App<Var<1>, Var<0>>>>,
              "two T f x ≡ f (f x), reduced symbolically");

// And the K combinator: (λa. λb. a) p q ≡ p, with p, q free.
using K_ = Lam<Star, Lam<Star, Var<1>>>;     // value-level approximation
using KApp = App<App<K_, Var<1>>, Var<0>>;
static_assert(equiv<KApp, Var<1>>, "K p q ≡ p, symbolically");

int main() { return 0; }
