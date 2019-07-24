(** * Theorems about [interp] *)

(** Main facts:
    - [unfold_interp]: Unfold lemma.
    - [interp_bind]: [interp] is a monad morphism.
    - [interp_trigger]: Events are interpreted using a handler.
 *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Basics
     Core.ITreeDefinition
     Core.KTree
     Core.KTreeFacts
     Eq.Eq
     Eq.UpToTaus
     Indexed.Sum
     Indexed.Function
     Indexed.Relation
     Interp.Interp
     Interp.Handler
     Interp.TranslateFacts.

Import ITreeNotations.
(* end hide *)

Instance Equivalence_eq_Handler {E F : Type -> Type}
  : Equivalence (@eq_Handler E F).
Proof.
  unfold eq_Handler.
  apply (Equivalence_i_pointwise (fun R => eq_itree eq)).
Qed.

Instance Equivalence_eutt_Handler {E F : Type -> Type}
  : Equivalence (@eutt_Handler E F).
Proof.
  unfold eutt_Handler.
  apply (Equivalence_i_pointwise (fun R => eutt eq)).
Qed.

Definition Equivalence_eq2_Handler {E F : Type -> Type}
  : @Equivalence (Handler E F) eq2.
Proof.
  exact Equivalence_eutt_Handler.
Qed.

(** Unfolding of [interp]. *)
Definition _interp {E F R} (f : E ~> itree F) (ot : itreeF E R _)
  : itree F R :=
  match ot with
  | RetF r => Tau (Ret r)
  | TauF t => Tau (interp f t)
  | VisF e k => ITree.gbind (f _ e) (fun x => interp f (k x))
  end.

(** Unfold lemma. *)
Lemma unfold_interp {E F R} {f : E ~> itree F} (t : itree E R) :
  interp f t ≅ (_interp f (observe t)).
Proof.
  unfold interp. unfold Basics.iter, MonadIter_itree. rewrite unfold_iter.
  destruct (observe t); cbn;
    rewrite ?bind_ret, ?gbind_map; reflexivity.
Qed.

(** ** [interp] and constructors *)

(** These are specializations of [unfold_interp], which can be added as
    rewrite hints.
 *)

Lemma interp_ret {E F R} {f : E ~> itree F} (x: R):
  interp f (Ret x) ≅ Tau (Ret x).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_tau {E F R} {f : E ~> itree F} (t: itree E R):
  eq_itree eq (interp f (Tau t)) (Tau (interp f t)).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_vis {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R) :
  eq_itree eq (interp f (Vis e k)) (ITree.gbind (f _ e) (fun x => interp f (k x))).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_trigger {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f (ITree.trigger e) ≳ f _ e.
Proof.
  unfold ITree.trigger. rewrite interp_vis.
  setoid_rewrite interp_ret.
  setoid_rewrite tau_eutt. rewrite eq_gbind_bind, bind_ret2.
  reflexivity.
Qed.

Hint Rewrite @interp_ret : itree.
Hint Rewrite @interp_vis : itree.
Hint Rewrite @interp_trigger : itree.

(** ** [interp] properness *)
Instance eq_itree_interp {E F}
  : @Proper (Handler E F -> (itree E ~> itree F))
            (eq_Handler ==> respectful_eq_itree)
            interp.
Proof.
  intros f g Hfg T.
  ginit. gcofix CIH with rr.
  intros l r Hlr.
  rewrite 2 unfold_interp.
  punfold Hlr; red in Hlr.
  destruct Hlr; cbn; subst; try discriminate; pclearbot.
  - do 2 (gstep; constructor); auto.
  - gstep; constructor; auto with paco.
  - eapply clo_gbind_; [ apply Hfg |].
    intros ? _ []; eauto with paco.
Qed.

Instance eq_itree_interp' {E F R f}
  : Proper (eq_itree eq ==> eq_itree eq) (@interp E (itree F) _ _ _ f R).
Proof.
  repeat red.
  eapply eq_itree_interp.
  reflexivity.
Qed.

Instance eutt_interp (E F : Type -> Type)
  : @Proper (Handler E F -> (itree E ~> itree F))
            (eq2 ==> respectful_eutt)
            interp.
Proof.
  repeat red.
  intros until T.
  ginit. gcofix CIH. intros.
  rewrite !unfold_interp. punfold H1. red in H1.
  induction H1; intros; subst; pclearbot; simpl.
  - do 2 (gstep; constructor). auto.
  - gstep; constructor. auto with paco.
  - eapply clo_gbind_; [eapply H|].
    intros ? _ []. eauto with paco.
  - rewrite tau_eutt, unfold_interp. auto.
  - rewrite tau_eutt, unfold_interp. auto.
Qed.

Instance euttge_interp (E F : Type -> Type)
  : @Proper (Handler E F -> (itree E ~> itree F))
            (i_pointwise (fun _ => euttge eq) ==>
             i_respectful (fun _ => euttge eq) (fun _ => euttge eq))
            interp.
Proof.
  repeat red.
  intros until T.
  ginit. gcofix CIH. intros.

  rewrite !unfold_interp. punfold H1. red in H1.
  induction H1; intros; subst; pclearbot; simpl.
  - do 2 (gstep; constructor). auto.
  - gstep; constructor. eauto with paco.
  - eapply clo_gbind_; [apply H|].
    intros ? _ []; eauto with paco.
  - rewrite tau_eutt, unfold_interp. auto.
  - discriminate.
Qed.

Instance euttge_interp' (E F : Type -> Type) (h : E ~> itree F) R
  : @Proper (itree E R -> itree F R)
            (euttge eq ==> euttge eq)
            (@interp _ _ _ _ _ h _).
Proof.
  repeat intro. apply euttge_interp; auto. reflexivity.
Qed.

Instance eutt_interp' {E F : Type -> Type} {R : Type} (f : E ~> itree F) :
  Proper (eutt eq ==> eutt eq)
         (@interp E (itree F) _ _ _ f R).
Proof.
  repeat red.
  apply eutt_interp.
  reflexivity.
Qed.

(* Proof of
   [interp f (t >>= k) ~ (interp f t >>= fun r => interp f (k r))]

   "By coinduction", case analysis on t:

    - [t = Ret r] or [t = Vis e k] (...)

    - [t = Tau t]:
          interp f (Tau t >>= k)
        = interp f (Tau (t >>= k))
        = Tau (interp f (t >>= k))
        { by "coinductive hypothesis" }
        ~ Tau (interp f t >>= fun ...)
        = Tau (interp f t) >>= fun ...
        = interp f (Tau t) >>= fun ...
        (QED)

 *)

Lemma interp_bind' {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
    ITree.bind (interp f t) (fun r => interp f (k r))
  ≳ interp f (ITree.bind t k).
Proof.
  revert R t k. ginit. gcofix CIH; intros.
  rewrite (unfold_bind t), (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite tau_eutt, bind_ret. apply reflexivity.
  - rewrite bind_tau, !interp_tau.
    gstep; econstructor. eauto with paco.
  - rewrite interp_vis, gbind_bind.
    eapply clo_gbind_; [reflexivity |].
    intros ? _ []. auto with paco.
Qed.

Lemma interp_bind {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
    interp f (ITree.bind t k)
  ≈ ITree.bind (interp f t) (fun r => interp f (k r)).
Proof. rewrite interp_bind'. reflexivity. Qed.

Lemma interp_gbind' {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
    ITree.gbind (interp f t) (fun r => interp f (k r))
  ≳ interp f (ITree.gbind t k).
Proof.
  rewrite (unfold_interp t); unfold ITree.gbind.
  destruct (observe t); cbn.
  - rewrite bind_ret, interp_tau. apply reflexivity.
  - rewrite interp_tau, interp_bind'; reflexivity.
  - rewrite interp_vis.
    match goal with
    | [ |- context E [ ITree._gbind (observe ?f) ?k ] ] =>
      fold (ITree.gbind f k)
    end.
    rewrite eq_gbind_bind, gbind_bind.
    ginit.
    eapply clo_gbind_; [reflexivity |].
    intros ? _ []. rewrite interp_bind'; apply reflexivity.
Qed.

Lemma interp_gbind {E F R S}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
    interp f (ITree.bind t k)
  ≈ ITree.gbind (interp f t) (fun r => interp f (k r)).
Proof. rewrite interp_gbind', eq_gbind_bind. reflexivity. Qed.

Hint Rewrite @interp_bind : itree.

(** *** Identities for [interp] *)

Lemma interp_id_h {A R} (t : itree A R)
  : interp (id_ A) t ≳ t.
Proof.
  revert t. ginit. gcofix CIH. intros.
  rewrite (itree_eta t), unfold_interp.
  destruct (observe t); cbn.
  - rewrite tau_eutt; apply reflexivity.
  - gstep; constructor; auto with paco.
  - gstep; constructor; intros.
    red. rewrite bind_ret. auto with paco.
Qed.

Lemma interp_trigger_h {E R} (t : itree E R) :
  interp ITree.trigger t ≈ t.
Proof.
  revert t. einit. ecofix CIH. intros.
  rewrite unfold_interp. rewrite (itree_eta t) at 2.
  destruct (observe t); cbn; try estep.
  - rewrite tau_eutt; apply reflexivity.
  - intros. rewrite bind_ret. auto with paco.
Qed.

(** ** Composition of [interp] *)

Theorem interp_interp' {E F G R} (f : E ~> itree F) (g : F ~> itree G) :
  forall t : itree E R,
      interp g (interp (fun _ e => Tau (f _ e)) t)
    ≈ interp (fun _ e => Tau (interp g (f _ e))) t.
Proof.
  ginit. gcofix CIH. intros.
  rewrite 2 (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite interp_tau. gstep; constructor.
    rewrite interp_ret, tau_eutt. apply reflexivity.
  - rewrite interp_tau. gstep; constructor. auto with paco.
  - rewrite interp_tau. gstep; constructor.
    (* TODO *)
Admitted.

Theorem interp_interp {E F G R} (f : E ~> itree F) (g : F ~> itree G) :
  forall t : itree E R,
      interp g (interp f t)
    ≈ interp (fun _ e => interp g (f _ e)) t.
Proof.
  intros. transitivity (interp g (interp (fun _ e => Tau (f _ e)) t)).
  - do 2 (eapply eutt_interp; try reflexivity).
    do 4 red; intros. rewrite tau_eutt; reflexivity.
  - rewrite interp_interp'.
    eapply eutt_interp; try reflexivity.
    do 4 red; intros. rewrite tau_eutt; reflexivity.
Qed.

Lemma interp_translate {E F G} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp g (translate f t) ≅ interp (fun _ e => g _ (f _ e)) t.
Proof.
  revert t.  
  ginit. gcofix CIH.
  intros t.
  rewrite !unfold_interp. unfold _interp.
  rewrite unfold_translate_. unfold translateF.
  destruct (observe t); cbn.
  - apply reflexivity. (* SAZ: typeclass resolution failure? *)
  - gstep. constructor. gbase. apply CIH.
  - eapply clo_gbind_.
    + reflexivity.
    + intros ? _ []. auto with paco.
Qed.

Lemma translate_to_interp {E F R} (f : E ~> F) (t : itree E R) :
  translate f t ≈ interp (fun _ e => ITree.trigger (f _ e)) t.
Proof.
  revert t. einit. ecofix CIH. intros.
  rewrite unfold_translate.
  rewrite unfold_interp.
  destruct (observe t); cbn.
  - rewrite tau_eutt. reflexivity.
  - estep.
  - unfold ITree.trigger. simpl.
    evis. intros. rewrite bind_ret. auto with paco.
Qed.

Lemma interp_forever {E F} (f : E ~> itree F) {R S}
      (t : itree E R)
  : interp f (ITree.forever t)
  ≈ @ITree.forever F R S (interp f t).
Proof.
  einit. ecofix CIH.
  rewrite (unfold_forever t), (unfold_forever (interp _ _)).
Admitted.

Lemma interp_iter' {E F} (f : E ~> itree F) {I A}
      (t  : I -> itree E (I + A))
      (t' : I -> itree F (I + A))
      (EQ_t : forall i, eq_itree eq (interp f (t i)) (t' i))
  : forall i,
    interp f (ITree.iter t i)
  ≅ ITree.iter t' i.
Proof.
  ginit. gcofix CIH; intros i.
  rewrite 2 unfold_iter.
  rewrite interp_gbind.
  guclo eqit_clo_bind; econstructor; eauto.
  { apply EQ_t. }
  intros [] _ []; cbn.
  - rewrite interp_tau; gstep; constructor; auto with paco.
  - rewrite interp_ret. gstep; constructor; auto.
Qed.

Lemma interp_iter {E F} (f : E ~> itree F) {A B}
      (t : A -> itree E (A + B)) a0
  : interp f (iter t a0) ≅ iter (fun a => interp f (t a)) a0.
Proof.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  apply interp_iter'.
  reflexivity.
Qed.

Lemma interp_loop {E F} (f : E ~> itree F) {A B C}
      (t : C + A -> itree E (C + B)) a :
  interp f (loop t a) ≅ loop (fun ca => interp f (t ca)) a.
Proof.
  unfold loop. unfold cat, Cat_Kleisli, ITree.cat; cbn.
  rewrite interp_bind.
  apply eqit_bind.
  repeat intro.
  rewrite interp_iter.
  apply eq_itree_iter.
  intros ? ? [].
  rewrite interp_bind.
  apply eqit_bind; try reflexivity.
  intros []; cbn. unfold cat. rewrite interp_bind.
  - unfold inl_, CoprodInl_Kleisli, inr_, CoprodInr_Kleisli, lift_ktree; cbn.
    rewrite interp_ret, !bind_ret, interp_ret.
    reflexivity.
  - unfold cat, id_, Id_Kleisli, inr_, CoprodInr_Kleisli, lift_ktree, pure; cbn.
    rewrite interp_bind, interp_ret, !bind_ret, interp_ret.
    reflexivity.
  - unfold inr_, CoprodInr_Kleisli, lift_ktree, pure; cbn.
    rewrite interp_ret.
    reflexivity.
Qed.
