(** * Interaction trees: core definitions *)

(* begin hide *)
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monad.
Require Import Program.Tactics.

From ITree Require Import Basics.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Set Contextual Implicit.

Set Printing Universes.
(* end hide *)

(** ** The type of interaction trees *)

(** An [itree E R] is the denotation of a program as coinductive
    (possibly infinite) tree where the leaves [Ret] are labeled with
    [R] and every node is either a [Tau] node with one child, or a
    branching node [Vis] with a _visible event_ [E X] that branches
    on the values of [X]. *)

Section itree.

  Universe uE uF uR uT.
  Context {E : Type@{uE} -> Type@{uF}} {R : Type@{uR}}.

  (** The type [itree] is defined as the final coalgebra ("greatest
      fixed point") of the functor [itreeF]. *)
  Variant itreeF (itree : Type@{uT}) :=
  | RetF (r : R)
  | TauF (t : itree)
  | VisF {X : Type@{uE}} (e : E X) (k : X -> itree)
  .

  (** We define non-recursive types such as [itreeF] using the [Variant]
      command. The main practical difference from [Inductive] is that
      [Variant] does not generate any induction schemes (which are
      unnecessary). *)

  CoInductive itree : Type@{uT} := go
  { _observe : itreeF itree }.

  (** A primitive projection, such as [_observe], must always be
      applied. To be used as a function, wrap it explicitly:
      [fun x => _observe x] or [observe] (defined below). *)

  (* Notes about using [itree]:

     - You should simplify using [cbn] rather than [simpl] when working
       with terms of the form [observe e] where [e] is defined by
       [CoFixpoint] (as in [bind] and [map] below).  [simpl] does not
       unfold the definition properly to expose the [observe t] term.

     - Once you have [observe t] as the subject of [match], you can
       [destruct (observe t)] to do the case split.
   *)

End itree.

(* begin hide *)
Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.
Local Open Scope itree_scope.

Arguments itree _ _ : clear implicits.
Arguments itreeF _ _ : clear implicits.
(* end hide *)

(** An [itree'] is a "forced" [itree]. It is the type of inputs
    of [go], and outputs of [observe]. *)
Notation itree' E R := (itreeF E R (itree E R)).

(** We wrap the primitive projection [_observe] in a function
    [observe]. *)
Definition observe@{uE uF uR uT} {E R} (t : itree@{uE uF uR uT} E R) : itree' E R := @_observe E R t.

(** Note that when [_observe] appears unapplied in an expression,
    it is implicitly wrapped in a function. However, there is no
    way to distinguish whether such wrapping took place, so relying
    on this behavior can lead to confusion.

    We recommend to always use a primitive projection applied,
    and wrap it in a function explicitly like the above to pass
    around as a first-order function. *)

(** We introduce notation for the [Tau], [Ret], and [Vis] constructors. Using
    notation rather than definitions works better for extraction.  (The [spin]
    definition, given below does not extract correctly if [Tau] is a definition.)

    Using this notation means that we occasionally have to eta expand, e.g.
    writing [Vis e (fun x => Ret x)] instead of [Vis e Ret]. (In this
    particular case, this is [ITree.trigger].)
*)
Notation Ret x := (go (RetF x)).
Notation Tau t := (go (TauF t)).
Notation Vis e k := (go (VisF e k)).

(** ** Main operations on [itree] *)

(** The core definitions are wrapped in a module for namespacing.
    They are meant to be used qualified (e.g., ITree.bind) or
    via notations (e.g., [>>=]). *)

(** *** How to write cofixpoints *)

(** We define cofixpoints in two steps: first a plain definition
    (prefixed with an [_], e.g., [_bind], [_iter]) defines the body
    of the function:

    - it takes the recursive call ([bind]) as a parameter;
    - if we are deconstructing an itree, this body takes
      the unwrapped [itreeF];

    second the actual [CoFixpoint] (or, equivalently, [cofix]) ties
    the knot, applying [observe] to any [itree] parameters. *)

(** This style allows us to keep [cofix] from ever appearing in
    proofs, which could otherwise get quite unwieldly.
    For every [CoFixpoint] (such as [bind]), we prove an unfolding
    lemma to rewrite it as a term whose head is [_bind], without
    any [cofix] above it.
[[
    unfold_bind : observe (bind t k)
                = observe (_bind (fun t' => bind t' k) t)
]]
    Note that this is an equality "up to" [observe]. It would not be
    provable if it were a plain equality:
[[
    bind t k = _bind (...) t  (* unfold the definition of [bind]... *)
    (cofix bind' t1 := _bind (...) t1) t = _bind (...) t1
]]
    The [cofix] is stuck, and can only be unstuck under the primitive
    projection [_observe] (which is wrapped by [observe]).
 *)

(** *** Definitions *)

(** These are meant to be imported qualified, e.g., [ITree.bind],
    [ITree.trigger], to avoid ambiguity with identifiers of the same
    name (some of which are overloaded generalizations of these).
 *)
Module ITree.

Section ITree.

Universe uE uF uR uT.
Context {E : Type@{uE} -> Type@{uF}}.

(** [bind]: monadic composition, tree substitution, sequencing of
    computations. [bind t k] is also denoted by [t >>= k] and using
    "do-notation" [x <- t ;; k x]. *)
Section bind.
  Context {T U : Type@{uR}}.

  (* We can keep the continuation outside the cofixpoint.
     In particular, this allows us to nest [bind] in other cofixpoints,
     as long as the recursive occurences are in the continuation
     (i.e., this makes it easy to define tail-recursive functions).
   *)
  Variable k : T -> itree@{uE uF uR uT} E U.

  Definition _bind
             (bind : itree E T -> itree E U)
             (oc : itreeF E T (itree E T)) : itree E U :=
    match oc with
    | RetF r => k r
    | TauF t => Tau (bind t)
    | VisF e h => Vis e (fun x => bind (h x))
    end.

  CoFixpoint bind' (t : itree@{uE uF uR uT} E T) : itree E U :=
    _bind bind' (observe t).

End bind.

Arguments _bind _ _ /.

Notation bind c k := (bind' k c).

(** Monadic composition of continuations (i.e., Kleisli composition).
 *)
Definition cat {T U V : Type@{uR}}
           (k : T -> itree@{uE uF uR uT} E U) (h : U -> itree E V)
  : T -> itree E V :=
  fun t => bind' h (k t).

(** [iter]: See [Basics.Basics.MonadIter]. *)

Definition _iter {R I : Type}
           (tau : _)
           (iter_ : I -> itree E R)
           (step_i : I + R) : itree E R :=
  match step_i with
  | inl i => tau (iter_ i)
  | inr r => Ret r
  end.

Definition iter {R I: Type@{uR}}
           (step : I -> itree E (I + R)) : I -> itree E R :=
  cofix iter_ i := bind (step i) (_iter (fun t => Tau t) iter_).

(* note(gmm): There needs to be generic automation for monads to simplify
 * using the monad laws up to a setoid.
 * this would be *really* useful to a lot of projects.
 *
 * this will be especially important for this project because coinductives
 * don't simplify very nicely.
 *)

(** Functorial map ([fmap] in Haskell) *)
Definition map {R S : Type@{uR}} (f : R -> S) (t : itree@{uE uF uR uT} E R)
  : itree E S :=
  bind t (fun x => Ret (f x)).

(** Atomic itrees triggering a single event. *)
Definition trigger : forall T : Type@{uE}, E T -> itree@{uE uF uR uT} E T :=
  fun R e => Vis e (fun x => Ret x).

(** Ignore the result of a tree. *)
Definition ignore {R} : itree E R -> itree E unit :=
  map (fun _ => tt).

(** Infinite taus. *)
CoFixpoint spin {R : Type@{uR}} : itree@{uE uF uR uT} E R := Tau spin.

(** Repeat a computation infinitely. *)
Definition forever {R S} (t : itree E R) : itree E S :=
  cofix forever_t := bind t (fun _ => Tau (forever_t)).

End ITree.

Notation bind c k := (bind' k c).

End ITree.

(** ** Notations *)

(** Sometimes it's more convenient to work without the type classes
    [Monad], etc. When functions using type classes are specialized,
    they simplify easily, so lemmas without classes are easier
    to apply than lemmas with.

    We can also make ExtLib's [bind] opaque, in which case it still
    doesn't hurt to have these notations around.
 *)

Module ITreeNotations.
Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 61, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 61, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 61, t1 at next level, p pattern, right associativity) : itree_scope.
Infix ">=>" := ITree.cat (at level 61, right associativity) : itree_scope.
End ITreeNotations.

(** ** Instances *)

Instance Functor_itree@{uE uF uR uT} {E : Type@{uE} -> Type@{uF}}
  : Functor (itree@{uE uF uR uT} E) :=
{ fmap := @ITree.map E }.

(* Instead of [pure := @Ret E], [ret := @Ret E], we eta-expand
   [pure] and [ret] to make the extracted code respect OCaml's
   value restriction. *)
Instance Applicative_itree@{uE uF uR uT} {E : Type@{uE} -> Type@{uF}}
  : Applicative (itree@{uE uF uR uT} E) :=
{ pure := fun _ x => Ret x
; ap := fun _ _ f x =>
          ITree.bind f (fun f => ITree.bind x (fun x => Ret (f x)))
}.

Instance Monad_itree@{uE uF uR uT} {E : Type@{uE} -> Type@{uF}}
  : Monad (itree@{uE uF uR uT} E) :=
{| ret := fun _ x => Ret x
;  bind := fun T U t k => @ITree.bind' E T U k t
|}.

Instance MonadIter_itree@{uE uF uR uT} {E}
  : MonadIter@{uR uT} (itree@{uE uF uR uT} E) :=
  fun _ _ => ITree.iter.

(** ** Tactics *)

(* [inv], [rewrite_everywhere], [..._except] are general purpose *)

Lemma hexploit_mp: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.
Ltac hexploit x := eapply hexploit_mp; [eapply x|].

Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.

Ltac inv H := inversion H; clear H; subst.

Ltac rewrite_everywhere lem :=
  progress ((repeat match goal with [H: _ |- _] => rewrite lem in H end); repeat rewrite lem).

Ltac rewrite_everywhere_except lem X :=
  progress ((repeat match goal with [H: _ |- _] =>
                 match H with X => fail 1 | _ => rewrite lem in H end
             end); repeat rewrite lem).

Ltac genobs x ox := remember (observe x) as ox.
Ltac genobs_clear x ox := genobs x ox; match goal with [H: ox = observe x |- _] => clear H x end.
Ltac simpobs := repeat match goal with [H: _ = observe _ |- _] =>
                    rewrite_everywhere_except (@eq_sym _ _ _ H) H
                end.

(** ** Compute with fuel *)

(** Remove [Tau]s from the front of an [itree]. *)
Fixpoint burn (n : nat) {E R} (t : itree E R) :=
  match n with
  | O => t
  | S n =>
    match observe t with
    | RetF r => Ret r
    | VisF e k => Vis e k
    | TauF t' => burn n t'
    end
  end.

Create HintDb itree discriminated.
