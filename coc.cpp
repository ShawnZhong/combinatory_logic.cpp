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
// (A) AST: terms-as-types, plus the Term concept that recognises them.
// =============================================================================
struct Star {};                                   // *
struct Box  {};                                   // □  (* : □)
template <int N>                  struct Var {};  // de Bruijn index
template <typename F, typename X> struct App {};  // F X

// Binder.  Lam and Pi share their structural recursion (lift, subst, nf-walk),
// so they share a constructor and differ only by a tag.  The rules that *do*
// distinguish them -- β-reduction (only Lam-headed App reduces) and inference
// (λ's type is a Π; Π's type is its codomain's sort) -- partial-specialize
// on the tag and stay sharp.  Construction-side, prefer the Lam / Pi aliases.
struct LamK {};                                                   // λ tag
struct PiK  {};                                                   // Π tag
template <class K> concept BindKind = std::is_same_v<K, LamK> || std::is_same_v<K, PiK>;

template <BindKind Kind, class A, class B> struct Bind {};        // gated by BindKind
template <class A, class B> using Lam = Bind<LamK, A, B>;         // λ:A. B
template <class A, class B> using Pi  = Bind<PiK,  A, B>;         // Π:A. B

template <class T>                      constexpr bool is_term_v                   = false;
template <>                             constexpr bool is_term_v<Star>             = true;
template <>                             constexpr bool is_term_v<Box>              = true;
template <int N>                        constexpr bool is_term_v<Var<N>>           = true;
template <class Kind, class A, class B> constexpr bool is_term_v<Bind<Kind, A, B>> = is_term_v<A> && is_term_v<B>;
template <class F, class X>             constexpr bool is_term_v<App<F, X>>        = is_term_v<F> && is_term_v<X>;

template <class T> concept Term = is_term_v<T>;

// =============================================================================
// (B) walk<Action, T, Depth> : structural fold over a term, threading the
//     current binder Depth and applying Action's per-Var rule at each variable
//     leaf.  Both lift and subst are instances of this scheme; the four-case
//     AST recursion is written exactly once.
// =============================================================================
template <class Action> concept VarAction = requires { typename Action::template at<0, 0>; };

template <class Action, class T, int Depth = 0> struct walk_ { using type = T; };  // Star, Box, …
template <VarAction Action, Term T, int Depth = 0> using walk = typename walk_<Action, T, Depth>::type;

template <class Action, int K, int Depth>            struct walk_<Action, Var<K>,    Depth>     { using type = typename Action::template at<K, Depth>; };
template <class Action, class A, class B, int Depth> struct walk_<Action, App<A, B>, Depth>     { using type = App<walk<Action, A, Depth>, walk<Action, B, Depth>>; };
template <class Action, class Kind, class A, class B, int Depth>
                                                     struct walk_<Action, Bind<Kind, A, B>, Depth> { using type = Bind<Kind, walk<Action, A, Depth>, walk<Action, B, Depth + 1>>; };

// =============================================================================
// (C) Walk actions.  Both lift and subst are instances of the walk scheme:
//     a tiny per-Var action plus a one-line alias that hands it to walk.
//     The four-case AST recursion lives in walk; everything below is just
//     "what to do at a variable, given the current binder depth."
//
//       lift<T, D, C>   : add D to every free var of T whose index is ≥ C.
//       subst<T, N, S>  : replace Var<N> in T with S, decrement free vars > N.
//                         β-rule: (Lam A B) X → subst<B, 0, X>.
//
//     Depth is threaded by walk; the actions consult it so the target Var
//     and the substituted term stay aligned with the surrounding context.
// =============================================================================
template <int Shift, int Cutoff> struct LiftA {
  template <int K, int Depth> using at = Var<K + Shift * (K >= Cutoff + Depth)>;
};
template <Term T, int Shift, int Cutoff = 0> using lift = walk<LiftA<Shift, Cutoff>, T>;

template <int Target, class Sub> struct SubstA {
  template <int K, int Depth>
  using at = std::conditional_t<(K == Target + Depth),
                                lift<Sub, Depth>,
                                Var<K - (K > Target + Depth)>>;
};
template <Term T, int Target, Term Sub> using subst = walk<SubstA<Target, Sub>, T>;

// =============================================================================
// (D) β-reduction.
//     whnf : reduce only redexes at the head.
//     nf   : full normal form -- whnf, then traverse subterms.
//     equiv: is_same on normal forms (β-equivalence; we skip η for now).
// =============================================================================
template <class T> struct whnf_ { using type = T; };
template <Term T> using whnf = typename whnf_<T>::type;

// App: reduce the head; if it's a Lam-headed binder, β-reduce, else leave neutral.
template <typename F, typename X> struct whnf_<App<F, X>> {
private:
  template <typename Fn> struct go { using type = App<Fn, X>; };
  template <typename A, typename B> struct go<Bind<LamK, A, B>> {
    using type = whnf<subst<B, 0, X>>;
  };
public:
  using type = typename go<whnf<F>>::type;
};

template <class T> struct nf_traverse_ { using type = T; };
template <Term T> using nf_traverse = typename nf_traverse_<T>::type;
template <Term T> using nf = nf_traverse<whnf<T>>;

template <class Kind, class A, class B> struct nf_traverse_<Bind<Kind, A, B>> {
  using type = Bind<Kind, nf<A>, nf<B>>;
};
template <typename F, typename X> struct nf_traverse_<App<F, X>> {
  using type = App<nf<F>, nf<X>>;
};

template <Term A, Term B>
inline constexpr bool equiv = std::is_same_v<nf<A>, nf<B>>;

// =============================================================================
// (E) Context as a variadic type pack (innermost first).  Var-lookup is
//     pack-indexed inline in infer_<Var<N>> below.
// =============================================================================
template <typename... Ts> struct Ctx {};

template <class T>    constexpr bool is_ctx_v             = false;
template <Term... Ts> constexpr bool is_ctx_v<Ctx<Ts...>> = true;
template <class C> concept Context = is_ctx_v<C>;

template <typename T, typename C> struct cons_;
template <typename T, typename... Ts> struct cons_<T, Ctx<Ts...>> {
  using type = Ctx<T, Ts...>;
};
template <Term T, Context C> using cons = typename cons_<T, C>::type;

// =============================================================================
// (F) Bidirectional infer.  App enforces argument-type equivalence via
//     static_assert; sort/well-formedness checks elided to keep the kernel
//     tight (callers verify by inspecting the inferred type).
// =============================================================================
template <class C, class T> struct infer_;
template <Context C, Term T> using infer = typename infer_<C, T>::type;

template <typename C> struct infer_<C, Star> { using type = Box; };

template <typename... Ts, int N> struct infer_<Ctx<Ts...>, Var<N>> {
  using type = lift<Ts...[N], N + 1>;
};

// Π's sort is the codomain's sort; we just synthesise it.
template <class C, class A, class B> struct infer_<C, Bind<PiK, A, B>> {
  using type = infer<cons<A, C>, B>;
};

// λ:A. B  has type  Π:A. (type of B in extended Γ)
template <class C, class A, class B> struct infer_<C, Bind<LamK, A, B>> {
  using type = Pi<A, infer<cons<A, C>, B>>;
};

// (F X) requires F : Π:A. T and X : A; result is T[X/0].
template <typename C, typename F, typename X> struct infer_<C, App<F, X>> {
private:
  template <typename FT> struct app_;
  template <typename A, typename T> struct app_<Bind<PiK, A, T>> {
    static_assert(equiv<A, infer<C, X>>, "App: argument type mismatch");
    using type = subst<T, 0, X>;
  };
public:
  using type = typename app_<whnf<infer<C, F>>>::type;
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
