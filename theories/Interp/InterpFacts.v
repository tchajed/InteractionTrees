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

Set Universe Polymorphism.
Set Printing Universes.
(* end hide *)

Instance Equivalence_eq_Handler@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}}
  : Equivalence (@eq_Handler@{uE uF uR uT} E F).
Proof.
  unfold eq_Handler.
  apply (Equivalence_i_pointwise (fun R => eq_itree eq)).
Qed.

Instance Equivalence_eutt_Handler@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}}
  : Equivalence (@eutt_Handler@{uE uF uR uT} E F).
Proof.
  unfold eutt_Handler.
  apply (Equivalence_i_pointwise (fun R => eutt eq)).
Qed.

Definition Equivalence_eq2_Handler@{uE uF uR uT uY uZ} {E F : Type@{uE} -> Type@{uF}}
  : @Equivalence (Handler@{uE uF uR uT} E F) eq2@{uY uZ}.
Proof.
  exact Equivalence_eutt_Handler.
Qed.

(** Unfolding of [interp]. *)
Definition _interp@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}} {R : Type@{uR}} (f : E ~> itree@{uE uF uR uT} F) (ot : itreeF E R _)
  : itree F R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp f t)
  | VisF e k => f _ e >>= (fun x => Tau (interp f (k x)))
  end.

(** Unfold lemma. *)
Lemma unfold_interp@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}} {R} {f : E ~> itree@{uE uF uR uT} F} (t : itree E R) :
  interp f t ≅ (_interp f (observe t)).
Proof.
  unfold interp. unfold Basics.iter, MonadIter_itree. rewrite unfold_iter.
  destruct (observe t); cbn;
    rewrite ?bind_ret, ?bind_map; reflexivity.
Qed.

(** ** [interp] and constructors *)

(** These are specializations of [unfold_interp], which can be added as
    rewrite hints.
 *)

Section T.
Universe uE uF uR uT.

Context {E F : Type@{uE} -> Type@{uF}}.
Context {R : Type@{uR}}.

Lemma interp_ret@{}
      {f : forall T : Type@{uE}, E T -> itree@{uE uF uR uT} F T} (x: R)
  : interp f (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_tau {f : forall T : Type@{uE}, E T -> itree F T} (t: itree@{uE uF uR uT} E R)
  : eq_itree eq (interp f (Tau t)) (Tau (interp f t)).
Proof. rewrite unfold_interp. reflexivity. Qed.

Lemma interp_vis@{} {f : forall T : Type@{uE}, E T -> itree@{uE uF uR uT} F T} (U : Type@{uE}) (e: E U) (k: U -> itree E R) :
  eq_itree eq (interp f (Vis e k)) (ITree.bind (f _ e) (fun x => Tau (interp f (k x)))).
Proof. rewrite unfold_interp. reflexivity. Qed.

End T.

Lemma interp_trigger@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}} {R : Type@{uE}} (f : forall T : Type@{uE}, E T -> itree@{uE uF uR uT} F T) (e : E R)
  : interp@{uE uF uR uT} f (ITree.trigger e) ≳ f R e.
Proof.
  unfold ITree.trigger. rewrite interp_vis.
  setoid_rewrite interp_ret.
  setoid_rewrite tau_eutt. rewrite bind_ret2.
  reflexivity.
Qed.

Hint Rewrite @interp_ret : itree.
Hint Rewrite @interp_vis : itree.
Hint Rewrite @interp_trigger : itree.

(** ** [interp] properness *)
Instance eq_itree_interp@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}}
  : @Proper (Handler@{uE uF uR uT} E F -> (itree E ~> itree F))
            (eq_Handler ==> respectful_eq_itree)
            interp@{uE uF uR uT}.
Proof.
  intros f g Hfg T.
  ginit. gcofix CIH with rr.
  intros l r Hlr.
  rewrite 2 unfold_interp.
  punfold Hlr; red in Hlr.
  destruct Hlr; cbn; subst; try discriminate; pclearbot; try (gstep; constructor; eauto with paco; fail).
  guclo eqit_clo_bind. econstructor; [eapply Hfg|].
  intros ? _ [].
  gstep; econstructor; eauto with paco.
Qed.

Instance eq_itree_interp'@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}} {R : Type@{uR}} {f : forall T : Type@{uE}, E T -> itree@{uE uF uR uT} F T}
  : Proper (eq_itree eq ==> eq_itree eq) (@interp E (itree F) _ _ _ f R).
Proof.
  repeat red.
  eapply eq_itree_interp.
  reflexivity.
Qed.

Instance eutt_interp@{uE uF uR uT uX} (E F : Type@{uE} -> Type@{uF})
  : @Proper (Handler@{uE uF uR uT} E F -> (itree@{uE uF uR uT} E ~> itree@{uE uF uR uT} F))
            (eq2@{uX _} ==> respectful_eutt)
            (@interp@{uE uF uR uT} E (itree@{uE uF uR uT} F) _ _ _).
Proof.
  repeat red.
  intros until T.
  ginit. gcofix CIH. intros.

  rewrite !unfold_interp. punfold H1. red in H1.
  induction H1; intros; subst; pclearbot; simpl.
  - gstep. constructor. eauto.
  - gstep. constructor. eauto with paco.
  - guclo eqit_clo_bind; econstructor; [apply H|].
    intros; subst.
    gstep; constructor; eauto with paco.
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
  - gstep. constructor. eauto.
  - gstep. constructor. eauto with paco.
  - guclo eqit_clo_bind; econstructor; [apply H|].
    intros; subst.
    gstep; constructor; eauto with paco.
  - rewrite tau_eutt, unfold_interp. auto.
  - discriminate.
Qed.

Instance eutt_interp' {E F : Type -> Type} {R : Type} (f : E ~> itree F) :
  Proper (eutt eq ==> eutt eq)
         (@interp E (itree F) _ _ _ f R).
Proof.
  repeat red. apply eutt_interp. reflexivity.
Qed.

Instance euttge_interp' {E F : Type -> Type} {R : Type} (f : E ~> itree F) :
  Proper (euttge eq ==> euttge eq)
         (@interp E (itree F) _ _ _ f R).
Proof.
  repeat red. apply euttge_interp. reflexivity.
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

Lemma interp_bind@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}} {R S : Type@{uR}}
      (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
    interp f (ITree.bind t k)
  ≅ ITree.bind'@{uE uF uR uT} (fun r => interp f (k r)) (interp f t).
Proof.
  revert R t k. ginit. gcofix CIH; intros.
  rewrite unfold_bind, (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite bind_ret. apply reflexivity.
  - rewrite bind_tau, !interp_tau.
    gstep. econstructor. eauto with paco.
  - rewrite interp_vis, bind_bind.
    guclo eqit_clo_bind; econstructor; try reflexivity.
    intros; subst.
    rewrite bind_tau. gstep; constructor; auto with paco.
Qed.

Hint Rewrite @interp_bind : itree.

(** *** Identities for [interp] *)

Typeclasses eauto := 6.

Lemma interp_id_h {A R} (t : itree A R)
  : interp (@id_ _ _ Id_Handler A) t ≳ t.
Proof.
  revert t. ginit. gcofix CIH. intros.
  rewrite (itree_eta t), unfold_interp.
  destruct (observe t); try (gstep; constructor; auto with paco).
  cbn. gstep. red; cbn. constructor; red; intros.
  rewrite bind_ret, tau_eutt. eauto with paco.
Qed.

Lemma interp_trigger_h {E R} (t : itree E R) :
  interp ITree.trigger t ≈ t.
Proof.
  revert t. einit. ecofix CIH. intros.
  rewrite unfold_interp. rewrite (itree_eta t) at 2.
  destruct (observe t); try estep.
  unfold ITree.trigger. simpl. rewrite bind_vis.
  evis. intros. rewrite bind_ret, tau_eutt.
  auto with paco.
Qed.

(** ** Composition of [interp] *)

Theorem interp_interp@{uE uF uR uT} {E F G : Type@{uE} -> Type@{uF}} {R}
        (f : E ~> itree F) (g : F ~> itree G) :
  forall t : itree E R,
      interp g (interp@{uE uF uR uT} f t)
    ≅ interp@{uE uF uR uT} (fun _ e => interp g (f _ e)) t.
Proof.
  ginit. gcofix CIH. intros.
  rewrite 2 (unfold_interp t).
  destruct (observe t); cbn.
  - rewrite interp_ret. gstep. constructor. reflexivity.
  - rewrite interp_tau. gstep. constructor. auto with paco.
  - rewrite interp_bind.
    guclo eqit_clo_bind.
    apply pbc_intro_h with (RU := eq).
    + reflexivity.
    + intros ? _ [].
      rewrite interp_tau.
      gstep; constructor.
      auto with paco.
Qed.

Lemma interp_translate@{uE uF uR uT} {E F G : Type@{uE} -> Type@{uF}} (f : E ~> F) (g : F ~> itree G) {R} (t : itree E R) :
  interp@{uE uF uR uT} g (translate f t) ≅ interp (fun _ e => g _ (f _ e)) t.
Proof.
  revert t.  
  ginit. gcofix CIH.
  intros t.
  rewrite !unfold_interp. unfold _interp.
  rewrite unfold_translate_. unfold translateF.
  destruct (observe t); cbn.
  - apply reflexivity. (* SAZ: typeclass resolution failure? *)
  - gstep. constructor. gbase. apply CIH.
  - guclo eqit_clo_bind; econstructor.
    + reflexivity.
    + intros ? _ []. gstep; constructor; auto with paco.
Qed.

Lemma translate_to_interp {E F R} (f : E ~> F) (t : itree E R) :
  translate f t ≈ interp (fun _ e => ITree.trigger (f _ e)) t.
Proof.
  revert t. einit. ecofix CIH. intros.
  rewrite unfold_translate.
  rewrite unfold_interp.
  destruct (observe t); try estep.
  unfold ITree.trigger. simpl. rewrite bind_vis.
  evis. intros. rewrite bind_ret, tau_eutt. auto with paco.
Qed.

Lemma interp_forever@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}} (f : E ~> itree F) {R S}
      (t : itree E R)
  : interp@{uE uF uR uT} f (ITree.forever t)
  ≅ @ITree.forever F R S (interp f t).
Proof.
  ginit. gcofix CIH.
  rewrite (unfold_forever t).
  rewrite (unfold_forever (interp _ _)).
  rewrite interp_bind.
  guclo eqit_clo_bind. econstructor; [reflexivity |].
  intros ? _ []. rewrite interp_tau.
  gstep. constructor; auto with paco.
Qed.

Lemma interp_iter'@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}}
      (f : forall T : Type@{uE}, E T -> itree F T) {I A : Type@{uR}}
      (t  : I -> itree E (I + A))
      (t' : I -> itree F (I + A))
      (EQ_t : forall i, eq_itree@{uE uF uR uT} eq (interp@{uE uF uR uT} f (t i)) (t' i))
  : forall i,
    interp@{uE uF uR uT} f (ITree.iter@{uE uF uR uT} t i)
  ≅ ITree.iter@{uE uF uR uT} t' i.
Proof.
  ginit. gcofix CIH; intros i.
  rewrite 2 unfold_iter.
  rewrite interp_bind.
  guclo eqit_clo_bind; econstructor; eauto.
  { apply EQ_t. }
  intros [] _ []; cbn.
  - rewrite interp_tau; gstep; constructor; auto with paco.
  - rewrite interp_ret. gstep; constructor; auto.
Qed.

Lemma interp_iter@{uE uF uR uT uY} {E F : Type@{uE} -> Type@{uF}} (f : forall T : Type@{uE}, E T -> itree F T) {A B : Type@{uR}}
      (t : A -> itree E (A + B)) a0
  : interp@{uE uF uR uT} f (iter@{uY _} t a0) ≅ iter (fun a => interp f (t a)) a0.
Proof.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  apply interp_iter'.
  reflexivity.
Qed.

Lemma interp_loop@{uE uF uR uT uY} {E F : Type@{uE} -> Type@{uF}}
      (f : forall T : Type@{uE}, E T -> itree F T) {A B C : Type@{uR}}
      (t : C + A -> itree E (C + B)) a :
  interp f (loop@{uY _} t a) ≅ loop@{uY _} (fun ca => interp f (t ca)) a.
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
