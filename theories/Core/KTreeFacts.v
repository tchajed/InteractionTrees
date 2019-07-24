(** * Facts about [aloop] and [loop] *)

(* begin hide *)
From Coq Require Import
     Program
     Classes.Morphisms
     Setoids.Setoid
     Relations.Relations.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.Function
     Core.ITreeDefinition
     Core.ITreeMonad
     Core.KTree
     Eq.Eq
     Eq.UpToTaus.

Import ITreeNotations.
Import CatNotations.
Local Open Scope itree.
(* end hide *)

(** ** [ITree.aloop] *)

Lemma bind_iter {E A B C} (f : A -> itree E (A + B)) (g : B -> itree E (B + C))
  : forall x,
    (ITree.iter f x >>= ITree.iter g)
  ≈ ITree.iter (fun ab =>
       match ab with
       | inl a => ITree.map inl (f a)
       | inr b => ITree.map (bimap inr (id_ _)) (g b)
       end) (inl x).
Proof.
  einit. ecofix CIH. intros.
  rewrite !unfold_iter. unfold ITree._iter.
  rewrite gbind_map, gbind_bind.
  assert (fff : forall r, euttG eq bot2 bot2 gL gH
    (
        x <-
        match r with
        | inl i => ITree.iter f i
        | inr r0 => Ret r0
        end;; ITree.iter g x)
    (
        ITree.iter
          (fun ab : A + B =>
           match ab with
           | inl a =>
               ITree.map inl (f a)
           | inr b =>
               ITree.map
                 (bimap inr (id_ C))
                 (g b)
           end) r)).
  { intro. destruct r.
    - admit.
    - rewrite bind_ret.
      revert b. ecofix CIH'. intros.
      rewrite 2 unfold_iter, gbind_map.
      assert (ggg : forall x0, euttG eq bot2 bot2 gL gH
    (ITree._iter (ITree.iter g) x0)
    (
        ITree._iter
          (ITree.iter
             (fun ab : A + B =>
              match ab with
              | inl a => ITree.map inl (f a)
              | inr b0 => ITree.map (bimap inr (id_ C)) (g b0)
              end)) (bimap inr (id_ C) x0))).
    { destruct x0; cbn.
      + admit.
      + reflexivity.
    }
Admitted.

Lemma clo_gbind_ {E X1 X2 R1 R2} (Rx : X1 -> X2 -> Prop) (RR : R1 -> R2 -> Prop)
      b1 b2 r
      (u1 : itree E X1) (u2 : itree E X2) (k1 : X1 -> itree E R1) (k2 : X2 -> itree E R2)
 : (eqit Rx b1 b2 u1 u2) ->
 (forall x1 x2, Rx x1 x2 ->
  gpaco2 (eqit_ RR b1 b2 id) (eqitC RR b1 b2) r r
    (k1 x1)
    (k2 x2))
 ->
 gpaco2 (eqit_ RR b1 b2 id) (eqitC RR b1 b2) bot2 r
    (ITree.gbind u1 k1)
    (ITree.gbind u2 k2).
Admitted.

Lemma eq_itree_iter' {E I1 I2 R1 R2}
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E (I1 + R1))
      (body2 : I2 -> itree E (I2 + R2))
      (eutt_body
       : forall j1 j2, RI j1 j2 -> eq_itree (sum_rel RI RR) (body1 j1) (body2 j2))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @eq_itree E _ _ RR (ITree.iter body1 i1) (ITree.iter body2 i2).
Proof.
  ginit. gcofix CIH. intros.
  do 2 rewrite unfold_iter.
  eapply clo_gbind_; [apply eutt_body; auto |].
  intros ? ? []; cbn.
  - eauto with paco.
  - gfinal. right. pfold. constructor; auto.
Qed.


Lemma gclo_gbind_ {E X1 X2 R1 R2} (Rx : X1 -> X2 -> Prop) (RR : R1 -> R2 -> Prop)
      gL gH
      (u1 : itree E X1) (u2 : itree E X2) (k1 : X1 -> itree E R1) (k2 : X2 -> itree E R2)
 : (eqit Rx true true u1 u2) ->
 (forall x1 x2, Rx x1 x2 ->
  euttG RR gL gL gL gH
    (k1 x1)
    (k2 x2))
 ->
 euttG RR bot2 bot2 gL gH
    (ITree.gbind u1 k1)
    (ITree.gbind u2 k2).
Admitted.

Lemma eutt_iter' {E I1 I2 R1 R2}
      (RI : I1 -> I2 -> Prop)
      (RR : R1 -> R2 -> Prop)
      (body1 : I1 -> itree E (I1 + R1))
      (body2 : I2 -> itree E (I2 + R2))
      (eutt_body
       : forall j1 j2, RI j1 j2 -> eutt (sum_rel RI RR) (body1 j1) (body2 j2))
  : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @eutt E _ _ RR (ITree.iter body1 i1) (ITree.iter body2 i2).
Proof.
  einit. ecofix CIH. intros.
  specialize (eutt_body i1 i2 RI_i).
  do 2 rewrite unfold_iter.
(*
  replace @ITree.gbind with (fun E X Y u v => @ITree.bind' E X Y v u); cbn.
  ebind; econstructor. eauto with paco.
*)
  eapply gclo_gbind_; cbn; eauto with paco.
  intros ? ? []; cbn; eauto with paco.
Qed.

(** ** [iter] *)

Lemma eqit_mon {E R1 R2} (RR RR' : R1 -> R2 -> Prop) b1 b2 :
  (RR <2= RR') ->
  (eqit RR b1 b2 <2= @eqit E _ _ RR' b1 b2).
Proof.
  intros.
  eapply paco2_mon_bot; eauto.
  intros ? ? ?. red.
  induction 1; auto.
Qed.

Instance eq_itree_iter {E A B} :
  @Proper ((A -> itree E (A + B)) -> A -> itree E B)
          ((eq ==> eq_itree eq) ==> pointwise_relation _ (eq_itree eq))
          iter.
Proof.
  intros body1 body2 EQ_BODY a. repeat red in EQ_BODY.
  unfold iter, Iter_Kleisli.
  eapply (eq_itree_iter' eq); auto.
  intros; eapply eqit_mon, EQ_BODY; auto.
  intros [] _ []; auto.
Qed.

Instance eutt_iter {E A B} :
  @Proper ((A -> itree E (A + B)) -> A -> itree E B)
          (pointwise_relation _ (eutt eq) ==> pointwise_relation _ (eutt eq))
          iter.
Proof.
  intros body1 body2 EQ_BODY a. repeat red in EQ_BODY.
  unfold iter, Iter_Kleisli.
  eapply (eutt_iter' eq); auto.
  intros ? _ []; eapply eqit_mon, EQ_BODY; auto.
  intros [] _ []; auto.
Qed.

Definition eutt_iter_gen {F A B R S} :
  @Proper ((A -> itree F (A + B)) -> A -> itree F B)
          ((R ==> eutt (sum_rel R S)) ==> R ==> (eutt S))
          KTree.iter.
Proof.
  do 3 red;
  intros body1 body2 EQ_BODY x y Hxy. red in EQ_BODY.
  eapply eutt_iter'; eauto.
Qed.

Instance eq2_ktree_iter {E A B} :
  @Proper (ktree E A (A + B) -> ktree E A B)
          (eq2 ==> eq2)
          iter.
Proof. apply eutt_iter. Qed.

Section KTreeIterative.

Lemma unfold_iter_ktree {E A B} (f : ktree E A (A + B)) (a0 : A) :
  iter f a0 ≅
    ITree.gbind (f a0) (fun ab =>
    match ab with
    | inl a => iter f a
    | inr b => Ret b
    end).
Proof.
  unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree, cat.
  rewrite unfold_iter; cbn.
  eapply eqit_gbind; reflexivity.
Qed.

Instance IterUnfold_ktree {E} : IterUnfold (ktree E) sum.
Proof.
  repeat intro.
  rewrite unfold_iter_ktree.
  do 2 red. rewrite eq_gbind_bind; reflexivity.
Qed.

Instance IterNatural_ktree {E} : IterNatural (ktree E) sum.
Proof.
  repeat intro.
  unfold bimap, Bimap_Coproduct, case_, CoprodCase_Kleisli, case_sum, cat, Cat_Kleisli.
  cbn.
  revert a0.
  einit. ecofix CIH. intros.
  rewrite 2 unfold_iter_ktree.
  rewrite gbind_bind.
  rewrite unfold_bind; unfold ITree.gbind.
  (* TODO: duplication *)
  destruct observe; cbn.
  - destruct r; cbn.
    + etau.
    + efinal.
      match goal with
      | [ |- context E [ ITree._gbind (observe ?f) ?k ] ] =>
        fold (ITree.gbind f k)
      end.
      rewrite tau_eutt, bind_ret, eq_gbind_bind, bind_bind.
      setoid_rewrite bind_ret. rewrite bind_ret2.
      reflexivity.
  - etau.
    rewrite bind_bind.
    ebind; econstructor; try reflexivity.
    intros [] ? [].
    + rewrite 2 bind_ret. auto with paco.
    + rewrite bind_ret, bind_bind. setoid_rewrite bind_ret. rewrite bind_ret2.
      reflexivity.
  - evis. intros.
    rewrite bind_bind.
    ebind; econstructor; try reflexivity.
    intros [] ? [].
    + rewrite 2 bind_ret. auto with paco.
    + rewrite bind_ret, bind_bind. setoid_rewrite bind_ret. rewrite bind_ret2.
      reflexivity.
Qed.

Lemma iter_dinatural_ktree {E A B C}
      (f : ktree E A (C + B)) (g : ktree E C (A + B)) (a0 : A)
  : iter (fun a =>
      cb <- Tau (f a) ;;
      match cb with
      | inl c => Tau (g c)
      | inr b => Ret (inr b)
      end) a0
  ≅ Tau (ITree.bind (f a0) (fun cb =>
     match cb with
     | inl c0 => iter (fun c =>
         ab <- Tau (g c) ;;
         match ab with
         | inl a => Tau (f a)
         | inr b => Ret (inr b)
         end) c0
     | inr b => Ret b
     end)).
Proof.
  revert A B C f g a0.
  ginit. gcofix CIH. intros.
  rewrite unfold_iter_ktree; cbn.
  rewrite bind_bind.
  gstep; constructor.
  guclo eqit_clo_bind. econstructor. try reflexivity.
  intros [] ? [].
  { rewrite bind_tau.
    (* TODO: here we should be able to apply symmetry and be done. *)
    rewrite unfold_iter_ktree; cbn.
    gstep; econstructor.
    rewrite bind_bind.
    guclo eqit_clo_bind; econstructor; try reflexivity.
    intros [] ? [].
    * rewrite bind_tau.
      eauto with paco.
    * rewrite bind_ret. gstep; econstructor; auto.
  }
  { rewrite bind_ret. gstep; constructor; auto. }
Qed.

Instance IterDinatural_ktree {E} : IterDinatural (ktree E) sum.
Proof.
  repeat intro.
  unfold bimap, Bimap_Coproduct, case_, CoprodCase_Kleisli, case_sum, cat, Cat_Kleisli.
  cbn.
  transitivity (iter (fun t =>
                        x <- Tau (f t);;
                        match x with
                        | inl a1 => Tau (g a1)
                        | inr b0 => Ret (inr b0)
                        end) a0).
  - apply eutt_iter; intros x.
    rewrite tau_eutt.
    eapply eutt_clo_bind.
    reflexivity.
    intros [] ? [].
    rewrite tau_eutt; reflexivity.
    reflexivity.
  - rewrite iter_dinatural_ktree.
    rewrite tau_eutt.
    eapply eutt_clo_bind.
    reflexivity.
    intros [] ? [].
    + apply eutt_iter; intros x.
      rewrite tau_eutt.
      eapply eutt_clo_bind.
      reflexivity.
      intros [] ? [].
      rewrite tau_eutt; reflexivity.
      reflexivity.
    + reflexivity.
Qed.

Lemma iter_codiagonal_ktree {E A B} (f : ktree E A (A + (A + B))) (a0 : A)
  : iter (iter (fun x => Tau (f x))) a0
  ≅ iter (fun a =>
       r <- Tau (f a) ;;
       match r with
       | inl a' => Ret (inl a')
       | inr (inl a') => Ret (inl a')
       | inr (inr b) => Ret (inr b)
       end) a0.
Proof.
  revert a0.
  ginit. gcofix CIH. intros.
  rewrite unfold_iter_ktree.
  rewrite (unfold_iter_ktree (fun _ => _ _ _)).
  rewrite unfold_iter_ktree; cbn.
  rewrite !bind_bind.
  gstep; constructor.
  guclo eqit_clo_bind. econstructor. reflexivity.
  intros [| []] ? [].
  - rewrite bind_ret.
    revert a.
    gcofix CIH'. intros.
    rewrite unfold_iter_ktree.
    rewrite (unfold_iter_ktree (fun _ => _ _ _)).
    cbn.
    rewrite bind_tau.
    gstep; constructor.
    rewrite !bind_bind.
    guclo eqit_clo_bind. econstructor. reflexivity.
    intros [| []] ? [].
    + rewrite bind_ret. auto with paco.
    + rewrite 2 bind_ret. auto with paco.
    + rewrite 2 bind_ret. gstep; reflexivity.
  - rewrite 2 bind_ret. auto with paco.
  - rewrite 2 bind_ret. gstep; reflexivity.
Qed.

Instance IterCodiagonal_ktree {E} : IterCodiagonal (ktree E) sum.
Proof.
  repeat intro.
  unfold bimap, Bimap_Coproduct, case_, CoprodCase_Kleisli, case_sum, cat, Cat_Kleisli.
  cbn.
  transitivity (iter (iter (fun x => Tau (f x))) a0).
  - apply eutt_iter. setoid_rewrite tau_eutt. reflexivity.
  - rewrite iter_codiagonal_ktree.
    apply eutt_iter.
    intros a1.
    rewrite tau_eutt.
    eapply eutt_clo_bind.
    + reflexivity.
    + intros [| []] ? []; rewrite ?tau_eutt; reflexivity.
Qed.

Global Instance Iterative_ktree {E} : Iterative (ktree E) sum.
Proof.
  split; typeclasses eauto.
Qed.

End KTreeIterative.
