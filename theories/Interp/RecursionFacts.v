(** * Properties of [Recursion.mrec] and [Recursion.rec]. *)

(** The main facts to take away are [mrec_as_interp] and [rec_as_interp]:
    [mrec] and [rec] are special cases of [interp], using [mrecursive] and
    [recursive] as handlers.
 *)

(* begin hide *)
From Coq Require Import
     Program.Tactics
     Setoid
     Morphisms
     RelationClasses.

Require Import Paco.paco.

From ITree Require Import
     Basics.Category
     Basics.Basics
     Basics.Function
     Core.ITreeDefinition
     Core.KTree
     Eq.Eq
     Eq.UpToTaus
     Indexed.Sum
     Indexed.Function
     Interp.Interp
     Interp.InterpFacts
     Interp.Recursion.

Import ITreeNotations.

Set Universe Polymorphism.
Set Printing Universes.
(* end hide *)

Section Facts.

Universe uE uF uR uT.
Context {D E : Type@{uE} -> Type@{uF}}
        (ctx : forall T : Type@{uE}, D T -> itree@{uE uF uR uT} (D +' E) T).

(** Unfolding of [interp_mrec]. *)

Definition _interp_mrec {R : Type@{uR}} (ot : itreeF@{uE uF uR uT} (D +' E) R _) : itree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (interp_mrec@{uE uF uR uT} ctx t)
  | VisF e k =>
    match e with
    | inl1 d => Tau (interp_mrec ctx (ctx _ d >>= k))
    | inr1 e => Vis e (fun x => Tau (interp_mrec ctx (k x)))
    end
  end.

Lemma unfold_interp_mrec R (t : itree (D +' E) R) :
  interp_mrec ctx t ≅ _interp_mrec (observe t).
Proof.
  unfold interp_mrec.
  rewrite unfold_iter.
  destruct observe; cbn.
  - rewrite bind_ret; reflexivity.
  - rewrite bind_ret; reflexivity.
  - destruct e; cbn.
    + rewrite bind_ret; reflexivity.
    + rewrite bind_vis.
      pstep; constructor. intros. left.
      rewrite bind_ret.
      apply reflexivity.
Qed.

(** [mrec ctx] is equivalent to [interp (mrecursive ctx)],
    where [mrecursive] is defined as follows. *)
Definition mrecursive (f : D ~> itree (D +' E))
  : (D +' E) ~> itree E :=
  case_ (mrec f) ITree.trigger.

Global Instance eq_itree_mrec {R} :
  Proper (eq_itree eq ==> eq_itree eq) (@interp_mrec _ _ ctx R).
Proof.
  ginit. gcofix CIH. intros.
  rewrite !unfold_interp_mrec.
  punfold H0. inv H0; try discriminate; pclearbot; simpobs; [| |destruct e]; gstep.
  - apply reflexivity.
  - econstructor. eauto with paco.
  - econstructor. gbase. eapply CIH. apply eqit_bind; auto; reflexivity.
  - econstructor. gstep; constructor. auto with paco.
Qed.

Theorem interp_mrec_bind {U T} (t : itree _ U) (k : U -> itree _ T) :
  interp_mrec ctx (ITree.bind t k) ≅
  ITree.bind (interp_mrec ctx t) (fun x => interp_mrec ctx (k x)).
Proof.
  revert t k; ginit. gcofix CIH; intros.
  rewrite (unfold_interp_mrec _ t).
  rewrite (unfold_bind t). (* TODO: should be [unfold_bind] but it is much slower *)
  destruct (observe t); cbn;
    [| |destruct e];
    autorewrite with itree.
  1: apply reflexivity.
  all: rewrite unfold_interp_mrec.
  all: try (gstep; econstructor; eauto with paco).
  - rewrite <- bind_bind; eauto with paco.
  - intros. red. rewrite bind_tau. gstep; constructor; auto with paco.
Qed.

Theorem interp_mrec_trigger {U} (a : (D +' E) U) :
    interp_mrec ctx (ITree.trigger a)
  ≳ mrecursive ctx _ a.
Proof.
  rewrite unfold_interp_mrec; unfold mrecursive.
  destruct a; cbn.
  rewrite tau_eutt, bind_ret2.
  reflexivity.
  pstep; constructor. intros; left. rewrite tau_eutt, unfold_interp_mrec; cbn.
  apply reflexivity.
Qed.

Theorem interp_mrec_as_interp {T} (c : itree _ T) :
  interp_mrec ctx c ≈ interp (mrecursive ctx) c.
Proof.
  rewrite <- (tau_eutt (interp _ _)).
  revert_until T. ginit. gcofix CIH. intros.
  rewrite unfold_interp_mrec, unfold_interp.
  destruct (observe c); [| |destruct e]; simpl; eauto with paco.
  - gstep; repeat econstructor; eauto.
  - gstep; constructor; eauto with paco.
  - rewrite interp_mrec_bind. unfold mrec.
    gstep; constructor.
    guclo eqit_clo_bind; econstructor; [reflexivity|].
    intros ? _ []; eauto with paco.
  - rewrite tau_eutt. unfold ITree.trigger, case_; simpl. rewrite bind_vis.
    gstep. constructor.
    intros; red.
    rewrite bind_ret. rewrite tau_eutt. auto with paco.
Qed.

Theorem mrec_as_interp {T} (d : D T) :
  mrec ctx d ≈ interp (mrecursive ctx) (ctx _ d).
Proof.
  apply interp_mrec_as_interp.
Qed.

Lemma interp_mrecursive {T : Type@{uE}} (d : D T) :
  interp@{uE uF uR uT} (mrecursive ctx) (trigger_inl1 d) ≈ mrec ctx d.
Proof.
  unfold mrecursive. unfold trigger_inl1.
  rewrite interp_trigger. cbn. reflexivity.
Qed.

Theorem unfold_interp_mrec_h@{uY} {T : Type@{uE}} (t : itree _ T)
  : interp_mrec ctx (interp (case_@{uY _} ctx inr_@{uY _}) t)
  ≈ interp_mrec ctx t.
Proof.
  rewrite <- tau_eutt.
  revert t. ginit; gcofix CIH. intros.
  rewrite (itree_eta t); destruct (observe t);
    try (rewrite 2 unfold_interp_mrec; cbn; gstep; repeat constructor; auto with paco; fail).
  rewrite interp_vis.
  rewrite (unfold_interp_mrec _ (Vis _ _)).
  destruct e; cbn.
  - rewrite 2 interp_mrec_bind.
    gstep; constructor.
    guclo eqit_clo_bind; econstructor; [reflexivity|].
    intros ? _ []; rewrite unfold_interp_mrec; cbn; auto with paco.
  - unfold inr_, Handler.Inr_sum1_Handler, Handler.Handler.inr_, Handler.Handler.htrigger.
    rewrite tau_eutt.
    rewrite bind_trigger, unfold_interp_mrec; cbn.
    gstep; constructor.
    intros; red. gstep; constructor.
    rewrite unfold_interp_mrec; cbn.
    auto with paco.
Qed.

End Facts.

Local Opaque interp_mrec.

Global Instance Proper_interp_mrec {D E} :
  @Proper ((D ~> itree (D +' E)) -> (itree (D +' E) ~> itree E))
          (Relation.i_pointwise (fun _ => eutt eq) ==>
           Relation.i_respectful (fun _ => eutt eq) (fun _ => eutt eq))
          interp_mrec.
Proof.
  intros f g Hfg R.
  ginit; gcofix CIH; intros t1 t2 Ht.
  rewrite 2 unfold_interp_mrec.
  punfold Ht; induction Ht; cbn; pclearbot.
  3: { destruct e; gstep; constructor.
    + gfinal; left. apply CIH.
      eapply eutt_clo_bind; eauto.
      intros ? _ []. auto.
    + gstep; constructor. auto with paco.
  }
  1,2: gstep; constructor; auto with paco.
  1,2: rewrite unfold_interp_mrec, tau_eutt; auto.
Qed.

Section rec_as_interp.

Universe uE uF uR uT uA uB.
Context {E : Type@{uE} -> Type@{uF}} {A : Type@{uA}} {B : Type@{uB}}.

(** [rec body] is equivalent to [interp (recursive body)],
    where [recursive] is defined as follows. *)
Definition recursive@{uY} (f : A -> itree@{uE uF uR uT} (callE A B +' E) B)
  : forall T : Type@{uE}, (callE A B +' E) T -> itree@{uE uF uR uT} E T :=
  case_@{uY _} (calling (rec f)) ITree.trigger.

Lemma rec_as_interp@{uY} (f : A -> itree (callE A B +' E) B) (x : A) :
  rec f x ≈ interp (recursive@{uY} f) (f x).
Proof.
  unfold rec.
  rewrite mrec_as_interp.
  apply eq_sub_eutt.
  eapply eq_itree_interp.
  - red. unfold case_; intros ? [[] | ]; reflexivity.
  - reflexivity.
Qed.

Lemma interp_recursive_call@{uY} (f : A -> itree (callE A B +' E) B) (x : A) :
   interp (recursive@{uY} f) (call@{uE uF uR uT _ _} x) ≈ rec f x.
Proof.
  unfold recursive. unfold call.
  rewrite interp_trigger. cbn.
  reflexivity.
Qed.

End rec_as_interp.

Section Proper.

Universe uE uF uR uT.

Global Instance euttge_interp_mrec {D E : Type@{uE} -> Type@{uF}} :
  @Proper ((D ~> itree (D +' E)) -> (itree (D +' E) ~> itree E))
          (Relation.i_pointwise (fun _ => euttge eq) ==>
           Relation.i_respectful (fun _ => euttge eq) (fun _ => euttge eq))
          interp_mrec@{uE uF uR uT}.
Proof.
  intros f g Hfg R.
  ginit; gcofix CIH; intros t1 t2 Ht.
  rewrite 2 unfold_interp_mrec.
  punfold Ht; induction Ht; cbn; pclearbot.
  3: { destruct e; gstep; constructor.
    + gfinal; left. apply CIH.
      eapply eqit_bind; auto. apply Hfg.
    + gstep; constructor. auto with paco.
  }
  1,2: gstep; constructor; auto with paco.
  1: rewrite unfold_interp_mrec, tau_eutt; auto.
  discriminate.
Qed.

Global Instance euttge_interp_mrec' {E D : Type@{uE} -> Type@{uF}} {R : Type@{uR}} (ctx : forall T : Type@{uE}, D T -> itree (D +' E) T) :
  Proper (euttge eq ==> euttge eq) (@interp_mrec@{uE uF uR uT} _ _ ctx R).
Proof.
  do 4 red. eapply euttge_interp_mrec. reflexivity.
Qed.

End Proper.
