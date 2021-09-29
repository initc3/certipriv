Require Import Coq.Logic.Epsilon.
Require Import Coq.Logic.ClassicalChoice. 
Require Export le_lift.
Require Export Reals.
Require Export Fourier.
Require Export EqObsRelDec.


Set Implicit Arguments.

Module Make (SemO:SEM_OPT).
 
 Module OPT2 := EqObsRelDec.Make SemO.
 Export OPT2.

 (* TODO: move this somewhere else *)
 Lemma deno_while_false_elim : forall E (e:E.expr T.Bool) c k (m:Mem.t k) f,
  E.eval_expr e m = false ->
  mu ([[ [while e do c] ]] E m) f == f m.
 Proof.
  intros; rewrite deno_while_elim, deno_cond_elim, H.
  apply deno_nil_elim.
 Qed.

 Lemma deno_cond_nil_elim : forall (e:E.expr T.Bool) E k (m:Mem.t k) f,
  mu ([[ [If e _then nil] ]] E m) f == f m.
 Proof.
  intros; rewrite deno_cond_elim.
  case (E.eval_expr e m); rewrite deno_nil_elim; trivial.
 Qed.

 Lemma deno_unroll_while_false_elim : forall (e:E.expr T.Bool) c E 
  k (m:Mem.t k) n f,
  E.eval_expr e m = false ->
  mu ([[unroll_while e c n]] E m) f == f m.
 Proof.
  intros; case n; unfold unroll_while.
  apply deno_cond_nil_elim.
  intro n'; fold (unroll_while e c n').
  rewrite deno_cond_elim, H, deno_nil_elim; trivial.
 Qed.
 
 Close Scope bool_scope.

 Lemma deno_while_split : forall k E e P c (m:Mem.t k) f,
  mu ([[ [while e do c] ]] E m) f ==
  mu ([[ [while (e && P) do c; while e do c] ]] E m) f.
 Proof.
  intros k E e P c m f.
  apply eq_distr_elim.
  rewrite (deno_while_bad e (!P)).
  rewrite deno_cons.
  symmetry; rewrite deno_cons.
  apply Mlet_eq_compat; [ | trivial].
  apply eq_distr_intro; intro.
  apply equiv_deno with Meq (Meq /-\ ~- EP1 (e && P) /-\ ~- EP2 (e && (!(!P)))).
  apply equiv_while; intros.
  simpl; unfold O.eval_op; simpl.
  rewrite negb_involutive; rewrite H; trivial.
  eapply equiv_strengthen; [ | apply equiv_eq_mem].
  unfold andR; intros; tauto.
  intros m1 m2 [Heq _]; rewrite Heq; trivial.
  trivial.
 Qed.

 Open Scope bool_scope.

 Lemma req_mem_self_upd_r : forall k (m:Mem.t k) t (x:Var.var t), 
  m = m{!x <-- m x!}.
 Proof.
  intros. 
  apply Mem.eq_leibniz; red; intros [t' x'].
  generalize (Var.eqb_spec x x'); case_eq (Var.eqb x x'); intros _ Heq.
  rewrite <-Heq, Mem.get_upd_same; trivial.
  rewrite  Mem.get_upd_diff; trivial.
 Qed.

 Lemma unroll_while_0_elim: forall e b c k (m:Mem.t k) f, 
  mu ([[ unroll_while b c 0%nat ]] e m) f == f m.
 Proof.
  unfold unroll_while; intros.
  rewrite deno_cond_elim.
  case (E.eval_expr b m); apply deno_nil_elim.
 Qed.

 Definition EP_eq_expr t (e1 e2:E .expr t) : mem_rel := 
  fun k (m1 m2:Mem.t k) => E.eval_expr e1 m1 = E.eval_expr e2 m2.

 Lemma Mlet_distr0_abs: forall (A B:Type) (F:A -> Distr B),
  Mlet (distr0 A) F == distr0 B. 
 Proof.
  intros.
  apply eq_distr_intro; intro f.
  rewrite Mlet_simpl.
  trivial.
 Qed.


 Section BOUNDED_LOOP.

  Variable c : cmd.

  Variable E : env.

  Variable b : E.expr T.Bool.

  Variable variant : E.expr T.Nat.

  Hypothesis Hvar: forall k (m:Mem.t k), E.eval_expr b m -> 
   range (EP k (variant <! (E.eval_expr variant m))) ([[c]] E m).

  Open Scope nat_scope.

  Lemma deno_bounded_while_elim : forall k n (m:Mem.t k) f,
   (forall m':Mem.t k, 
    E.eval_expr variant m' = 0%nat -> E.eval_expr b m' = false) ->
   E.eval_expr variant m <= n ->
   mu ([[ [while b do c] ]] E m) f == 
   mu (drestr ([[ unroll_while b c n ]] E m) (negP (@EP k b))) f.
  Proof.
   induction n using lt_wf_ind; induction n.
   (* base case *)
   intros m f Hb Hm.
   rewrite (deno_while_false_elim _ _ _ _ _ (Hb _ (eq_sym (le_n_0_eq _ Hm)))).
   unfold drestr, negP, EP, negb; rewrite Mlet_simpl.
   rewrite (deno_unroll_while_false_elim _ _ _ _ _ _ 
    (Hb _ (eq_sym (le_n_0_eq _ Hm)))).
   rewrite Hb; auto with arith.
   (* inductive case *)
   intros m f Hb Hn'.
   unfold drestr; rewrite Mlet_simpl.
   unfold unroll_while; fold (unroll_while b c n).
   rewrite deno_while_elim.
   repeat rewrite deno_cond_elim; case_eq (E.eval_expr b m); intro Heq.
   repeat rewrite deno_app_elim.
   apply range_eq with (1:=Hvar _ Heq).
   intros m' Hm'; rewrite (H n); auto.
   generalize Hn' Hm'; clear Hn' Hm'; unfold EP; rewrite <- eval_lt;
    change (E.eval_expr (E.eval_expr variant m) m') with (E.eval_expr variant m).
   omega.
   unfold negP, EP, negb.
   rewrite deno_nil_elim, deno_nil_elim, Heq; trivial.
  Qed.

  Lemma lossless_bounded_while :
   lossless E c ->
   lossless E [while b do c].
  Proof.
   intros Hloss k.
   assert (forall (n:nat) (m : Mem.t k), E.eval_expr variant m = n ->
    (mu ([[ [while b do c] ]] E m)) (@fone _) == 1%U).
   induction n using lt_wf_ind;intros.
   rewrite deno_while_elim, deno_cond_elim.
   case_eq (E.eval_expr b m); intros Heq; [ | rewrite deno_nil_elim; trivial].
   rewrite deno_app_elim, <- (Hloss k m).
   apply range_eq with (1:=Hvar m Heq).
   intros m' Hlt; apply (H (E.eval_expr variant m')); trivial.
   rewrite <- H0; unfold EP in Hlt; simpl in Hlt; unfold O.eval_op in Hlt.
   simpl in Hlt.
   apply leb_complete in Hlt; omega.
   intros m;apply (H (E.eval_expr variant m) m (refl_equal _)).
  Qed.

  Close Scope nat_scope.

 End BOUNDED_LOOP.

 Close Scope R_scope.

Section Sym_Logic.

 Definition eequiv (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) 
  (lam:nat -> R) (ep:nat-o>U) :=
  forall k m1 m2,
   sig (fun d => 
    P k m1 m2 -> 
    le_lift (Q k) d ([[c1]] E1 m1) ([[c2]] E2 m2) (lam k) (ep k)).

 Lemma equiv_eequiv : forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel),
  equiv P E1 c1 E2 c2 Q -> eequiv P E1 c1 E2 c2 Q (fun _ => R1) (fzero _).
 Proof.
  unfold eequiv, equiv; intros.
  apply constructive_indefinite_description.
  destruct (H k) as (d,Hd).
  exists (d m1 m2); intros; rewrite le_lift_lift; auto.
 Qed.

 Lemma eequiv_equiv : forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel),
  eequiv P E1 c1 E2 c2 Q (fun _ => R1) (fzero _) -> equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold eequiv, equiv; intros.
  cut (exists d, forall mm:(Mem.t k * Mem.t k),
   P k (fst mm) (snd mm) -> 
   lift (Q k) (d mm) (([[ c1 ]]) E1 (fst mm)) (([[ c2 ]]) E2 (snd mm))).
  intros (d,Hd); exists (fun m1 m2 => d (m1,m2)).
  intros m1 m2 Hm; apply (Hd (m1,m2) Hm).
  destruct (choice (fun (mm:Mem.t k * Mem.t k) (dd:Distr(Mem.t k * Mem.t k)) =>  
   P k (fst mm) (snd mm) ->
   lift (Q k) dd (([[ c1 ]]) E1 (fst mm)) (([[ c2 ]]) E2 (snd mm)))) as (d',Hd').
  intros (m1,m2); destruct (X _ m1 m2) as (d,Hd).
  exists d; simpl; intro; rewrite <-le_lift_lift; auto.
  eauto.
 Qed.

 Lemma eequiv_deno : forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) lam ep,
  eequiv P E1 c1 E2 c2 Q lam ep ->
  forall k (f g : Mem.t k -> U),
  (forall m1 m2 : Mem.t k, Q k m1 m2 -> f m1 == g m2) ->
  forall m1 m2 : Mem.t k,
  P k m1 m2 -> 
  d_expr ([[ c1 ]] E1 m1) ([[ c2 ]] E2 m2) (lam k) f g <= (ep k).
 Proof.
  unfold eequiv; intros.
  destruct (X k m1 m2) as [d Hd]; trivial.
  apply le_lift_elim with (Q k) d; auto.  
 Qed.     

 Lemma eequiv_sdeno : forall c1 E1 c2 E2 (P Q:mem_rel) ep ep' lam lam'
  k (d1 d2 : Distr(Mem.t k)),
  (forall k, 1 <= lam' k)%R ->
  is_Discrete d1 ->
  is_Discrete d2 ->
  eequiv P E1 c1 E2 c2 Q lam' ep' ->
  (exists d, le_lift (@P k) d d1 d2 (lam k) (ep k)) ->
  forall f g,
  (forall m1 m2 : Mem.t k, Q k m1 m2 -> f m1 == g m2) ->
  d_expr (Mlet d1 ([[c1]] E1)) (Mlet d2 ([[c2]] E2)) (lam k * lam' k) f g <= 
  max (ep k + lam k ** ep' k) (ep' k + lam' k ** ep k).
 Proof.
  unfold eequiv; intros; destruct H0 as [d Hd].
  apply le_lift_elim with (S:=Q k) 
   (d:=Mlet d (fun mm => proj1_sig (X1 _ (fst mm) (snd mm)))); trivial.
  apply le_lift_Mlet with 
   (P k) (fun ab ab' => mem_eqU (fst ab) (fst ab') * mem_eqU (snd ab) (snd ab')).
  apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
  refine (le_lift_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) X X0 Hd).
  trivial.
  trivial.
  intros m1 m2 Hm; simpl; destruct (X1 k m1 m2) as (d', Hd'); auto.
 Qed.

 Lemma eequiv_weaken : 
  forall P E1 c1 E2 c2 Q lam ep P' Q' (lam':nat -> R) (ep':nat -o> U),
   implMR P P' ->
   implMR Q' Q ->
   (forall x, (lam' x <= lam x)%R) ->
   ep' <= ep ->
   eequiv P' E1 c1 E2 c2 Q' lam' ep' ->
   eequiv P  E1 c1 E2 c2 Q  lam ep.
 Proof.
  unfold eequiv; intros.
  destruct (X _ m1 m2) as (d,Hd); clear X.
  exists d.
  intros Hm; apply le_lift_weaken with (Q' k) (lam' k) (ep' k); auto.
 Qed.

 Lemma eequiv_eq_compat_l : forall (P Q:mem_rel) E1 E2 c1 c1' c2 lam ep,
  (forall k (m1 m2:Mem.t k) f, 
   P k m1 m2 -> mu ([[c1]] E1 m1) f == mu ([[c1']] E1 m1) f) ->
  eequiv P E1 c1  E2 c2  Q lam ep ->
  eequiv P E1 c1' E2 c2 Q lam ep.
 Proof.
  intros P Q E1 E2 c1 c1' c2 lam ep Heq Hequiv k m1 m2.
  destruct (Hequiv k m1 m2) as [d Hd].
  exists d; intros.
  assert (X:=fun f => Heq k m1 m2 f H).
  apply eq_distr_intro in X.
  rewrite <-X. auto.
 Qed. 

 Lemma eequiv_eq_compat_r : forall (P Q:mem_rel) E1 E2 c1 c2 c2' lam ep,
  (forall k (m1 m2:Mem.t k) f, 
   P k m1 m2 -> mu ([[c2]] E2 m2) f == mu ([[c2']] E2 m2) f) ->
  eequiv P E1 c1 E2 c2  Q lam ep ->
  eequiv P E1 c1 E2 c2' Q lam ep.
 Proof.
  intros P Q E1 E2 c1 c2 c2' lam ep Heq Hequiv k m1 m2.
  destruct (Hequiv k m1 m2) as [d Hd].
  exists d; intros.
  assert (X:=fun f => Heq k m1 m2 f H).
  apply eq_distr_intro in X.
  rewrite <-X; auto.
 Qed. 

 Lemma eequiv_trueR : forall (P:mem_rel) E1 c1 E2 c2 (lam:nat -> R) ep1 ep2,
  (forall k, 1 <= lam k)%R ->
  (forall k (m1 m2:Mem.t k), P _ m1 m2 ->
   ep1 k <=  mu ([[c1]] E1 m1) (fone _) /\
   ep2 k <=  mu ([[c2]] E2 m2) (fone _)) ->
  eequiv P E1 c1 E2 c2 trueR lam (fun k => [1-] (lam k ** min (ep1 k) (ep2 k))).
 Proof.
  unfold eequiv; intros.
  exists (prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2)).
  intros Hm.
  eapply le_lift_weaken; [ | | | apply 
   (@le_lift_true _ _ ([[c1]] E1 m1) ([[c2]] E2 m2) (lam k)) ]; trivial.
  apply Uinv_le_compat; apply multRU_le_compat; trivial.
  transitivity 1%R; auto with real.
  destruct (H0 _ _ _ Hm); trivial.
  apply min_le_compat; trivial.
 Qed.

 Lemma eequiv_trueR_lossless : forall (P:mem_rel) E1 c1 E2 c2,
  lossless E1 c1 -> 
  lossless E2 c2 -> 
  eequiv P E1 c1 E2 c2 trueR (fun _ => R1) (fzero _).
 Proof.
  intros.
  eapply eequiv_weaken; [ | | | |  
   apply (eequiv_trueR P E1 c1 E2 c2 (fun _ => 1%R) (fone _) (fone _)) ]; trivial.
  unfold fzero, fone; refine (ford_le_intro _); intro k;
   rewrite multRU_1_l, min_eq_right; auto.
  split; [ rewrite (H _ m1) | rewrite (H0 _ m2) ]; trivial.
 Qed.

 Lemma eequiv_falseR : forall E1 c1 E2 c2 Q,
  eequiv falseR E1 c1 E2 c2 Q (fun _ => R1) (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (distr0 _).
  unfold falseR; intros H; tauto.
 Qed.

 Hint Resolve eequiv_falseR.

 Lemma eequiv_transp : forall P E1 c1 E2 c2 Q lam ep,
  eequiv (transpR P) E2 c2 E1 c1 (transpR Q) lam ep ->
  eequiv P E1 c1 E2 c2 Q lam ep.
 Proof.
  unfold eequiv, transpR; intros.
  destruct (X k m2 m1) as [d Hd]; clear X.
  exists (Mlet d (fun mm => Munit (snd mm, fst mm))).
  intros.
  apply le_lift_transp.
  eapply le_lift_eq_compat with (6:=Hd H); auto.
  rewrite Mcomp, <-(Mext d) at 1.
  apply Mlet_eq_compat; trivial.
  refine (ford_eq_intro _); intros (m1',m2'); auto.
 Qed.
 
 Lemma eequiv_sym : forall P E1 c1 E2 c2 Q lam ep,
  symMR P ->
  symMR Q ->
  eequiv P E2 c2 E1 c1 Q lam ep ->
  eequiv P E1 c1 E2 c2 Q lam ep.
 Proof.
  intros P E1 c1 E2 c2 Q lam ep (HP,_) (_,HQ) H.
  apply eequiv_transp.
  eapply eequiv_weaken with (5:=H); trivial.
 Qed.

 Lemma eequiv_case : forall (P P':mem_rel) E1 c1 E2 c2 Q lam ep,
  decMR P' ->
  eequiv (P /-\ P') E1 c1 E2 c2 Q lam ep ->
  eequiv (P /-\ ~-P') E1 c1 E2 c2 Q lam ep ->
  eequiv P E1 c1 E2 c2 Q lam ep. 
 Proof.
  unfold andR, notR, eequiv; intros.
  destruct (X0 _ m1 m2) as (dt,Hdt); destruct (X1 _ m1 m2) as (df,Hdf).
  destruct (X k m1 m2); [ exists dt | exists df ]; auto.
 Qed.

 Lemma eequiv_nil : forall P E1 E2, 
  eequiv P E1 (@nil I.instr) E2 (@nil I.instr) P (fun _ => R1) (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (Munit (m1, m2)); intros.
  rewrite deno_nil, deno_nil.
  apply (le_lift_Munit _ _ _ (Rle_refl _) H).
 Qed.

 Lemma eequiv_seq : forall (P:mem_rel) E1 c1 E2 c2 Q' lam ep Q c1' c2' lam' ep',
  (forall k, 1 <= lam' k)%R ->
  eequiv P E1 c1  E2 c2 Q' lam ep ->
  eequiv Q' E1 c1' E2 c2' Q lam' ep' ->
  eequiv P E1 (c1 ++ c1') E2 (c2 ++ c2') Q (fun k => lam k * lam' k)%R 
  (fun k => max (ep k + lam k ** ep' k) (ep' k + lam' k ** ep k)).
 Proof.
  unfold eequiv; intros.
  destruct (X _ m1 m2) as (d, Hd).
  exists (Mlet d (fun mm => proj1_sig (X0 _ (fst mm) (snd mm)))). 
  intro Hm.
  rewrite deno_app, deno_app.
  apply le_lift_Mlet with (Q' k)
   (fun ab ab' => mem_eqU (fst ab) (fst ab') * mem_eqU (snd ab) (snd ab')).
  apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
  refine (le_lift_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) 
   (sem_discr _ _ _) (sem_discr _ _ _) (Hd Hm)).
  trivial.
  auto.
  intros m1' m2' Hm'; simpl; destruct (X0 _ m1' m2') as (d', Hd'); auto.
 Qed.

Lemma eequiv_seq_rlossless: forall (P:mem_rel) E1 c1 E2 c2 Q' lam ep Q c1' c2' lam' ep',
  (forall k, 1 <= lam' k)%R ->
  decMR Q' ->
  (forall k (m1 m2:Mem.t k), ~ Q' _ m1 m2 -> mu ([[ c1' ]] E1 m1) (fone _)== 1%U /\
    mu ([[ c2' ]] E2 m2) (fone _) == 1%U ) ->
  eequiv P E1 c1  E2 c2 Q' lam ep ->
  eequiv Q' E1 c1' E2 c2' Q lam' ep' ->
  eequiv P E1 (c1 ++ c1') E2 (c2 ++ c2') Q (fun k => lam k * lam' k)%R 
  (fun k => ep k + ep' k).
 Proof.
  unfold eequiv; intros.
  destruct (X0 _ m1 m2) as (d, Hd).
  exists (Mlet d (fun mm => if X _ (fst mm) (snd mm) then
    proj1_sig (X1 _ (fst mm) (snd mm)) else
    prod_distr ([[ c1' ]] E1 (fst mm)) ([[ c2' ]] E2 (snd mm)))).
  intro Hm.
  rewrite 2 deno_app.
  eapply le_lift_Mlet_discr_lossless with (R2:=Q' k) (carA1:=@mem_eqU k)
    (carA2:=@mem_eqU k) (carB1:=@mem_eqU k) (carB2:=@mem_eqU k); 
    trivial; try (apply mem_eqU_spec || apply sem_discr).
    apply (Hd Hm).
    intros m1' m2' Hm'; simpl; destruct (X k m1' m2') as [ _ | ? ];
      [ | tauto ].
    destruct (X1 _ m1' m2') as (d', Hd'); auto.
    intros m1' m2' Hm'; simpl; destruct (X k m1' m2') as [ H' | _ ]; 
      [ tauto | trivial ].
    intros m1' m2' Hm'; destruct (H0 _ _ _ Hm'); auto.
 Qed.

 Lemma eequiv_seq_strong: forall (P:mem_rel) E1 c1 E2 c2 Q' lam ep Q c1' c2' lam' ep',
  (forall k, 1 <= lam' k)%R ->
  decMR Q' ->
  lossless E1 c1' ->
  lossless E2 c2' ->
  eequiv P E1 c1  E2 c2 Q' lam ep ->
  eequiv Q' E1 c1' E2 c2' Q lam' ep' ->
  eequiv P E1 (c1 ++ c1') E2 (c2 ++ c2') Q (fun k => lam k * lam' k)%R 
  (fun k => ep k + ep' k).
 Proof.
  intros.
  apply eequiv_seq_rlossless with (Q':=Q'); trivial.
  intros; split; [ apply H0 | apply H1].
 Qed.


 Lemma eequiv_seq_full: forall (P:mem_rel) E1 c1 E2 c2 Q' lam ep Q c1' c2' lam' ep',
  (forall k, 1 <= lam' k)%R ->
  decMR Q' ->
  (forall k (m1:Mem.t k), exists m2, Q' _ m1 m2) ->
  (forall k (m2:Mem.t k), exists m1, Q' _ m1 m2) ->
  eequiv P E1 c1  E2 c2 Q' lam ep ->
  eequiv Q' E1 c1' E2 c2' Q lam' ep' ->
  eequiv P E1 (c1 ++ c1') E2 (c2 ++ c2') Q (fun k => lam k * lam' k)%R 
  (fun k => ep k + ep' k).
 Proof.
  unfold eequiv; intros.
  destruct (X0 _ m1 m2) as (d, Hd).
  exists (Mlet d (fun mm => if X _ (fst mm) (snd mm) then
    proj1_sig (X1 _ (fst mm) (snd mm)) else distr0 _)).
  intro Hm.
  rewrite 2 deno_app.
  destruct (choice _ (H0 k)) as (Fl, HFl).
  destruct (choice _ (H1 k)) as (Fr, HFr).
  eapply le_lift_Mlet_discr_full with (R2:=Q' k) (carA1:=@mem_eqU k)
    (carA2:=@mem_eqU k) (carB1:=@mem_eqU k) (carB2:=@mem_eqU k) (FAB:=Fl) (FBA:=Fr); 
    trivial; try (apply mem_eqU_spec || apply sem_discr).
    apply (Hd Hm).
    intros m1' m2' Hm'; simpl; destruct (X k m1' m2') as [ _ | ? ];
      [ | tauto ].
    destruct (X1 _ m1' m2') as (d', Hd'); auto.
 Qed.


 Lemma eequiv_frame : forall (P Q I:mem_rel) E1 c1 E2 c2 del ep,
  (forall k (m1 m2:Mem.t k), 
   I _ m1 m2 -> range (prodP (@I k)) (prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2))) ->
  eequiv P E1 c1 E2 c2 Q del ep ->
  eequiv (P /-\ I) E1 c1 E2 c2 (Q /-\ I) del ep.
 Proof.
  intros; intros k m1 m2.
  destruct (X _ m1 m2) as [d Hd].
  exists d; intros (HP,HI).
  pose proof (le_lift_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)
   (sem_discr _ _ _) (sem_discr _ _ _) (Hd HP)) as Hd_discr.
  destruct (Hd HP); clear Hd.
  constructor; trivial; clear le_lam le_d.
  unfold prodP, andR; apply (range_discr_strengthen Hd_discr _
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)) le_r). 
  apply (range_discr_intro _ Hd_discr _
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k))).
  intros mm Hmm.
  apply (range_discr_elim _ 
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)) (H _ _ _ HI)).
  intro H'; elim Hmm.
  assert (Haux: mu ([[ c1 ]] E1 m1) (fun m =>  mem_eqU (fst mm) m) *
   mu ([[ c2 ]] E2 m2) (fun m =>  mem_eqU (snd mm) m) == 0); [ | clear H' ].
  unfold prod_distr in H'; rewrite Mlet_simpl in H'; simpl in H'.
  rewrite Umult_sym, <-(mu_stable_mult (([[ c1 ]]) E1 m1) 
   (mu ([[ c2 ]] E2 m2) (fun m =>  mem_eqU (snd mm) m))), H'.
  apply mu_stable_eq; unfold fmult; refine (ford_eq_intro _); intro m.
  rewrite Umult_sym; symmetry.
  apply (mu_stable_mult (([[ c2 ]]) E2 m2) (mem_eqU (fst mm) m)).
  symmetry; apply Ule_zero_eq;  unfold Mfst, Msnd in *.
  apply (Ueq_orc ( mu ([[ c1 ]] E1 m1) (fun m =>  mem_eqU (fst mm) m)) 0); 
   [ auto | | ]; intro Hc1.
  rewrite <-Hc1, <-le_p1, Mlet_simpl.
  apply mu_monotonic; refine (ford_le_intro _); intro m'; auto.
  rewrite (Umult_zero_simpl_right (Oeq_sym Haux) (neq_sym Hc1)), 
   <-le_p2, Mlet_simpl.
  apply mu_monotonic; refine (ford_le_intro _); intro m'; auto.
 Qed.
 
 Lemma eequiv_range : forall (P Q I:mem_rel) E1 c1 E2 c2 del ep,
  (forall k (m1 m2:Mem.t k), 
   P k m1 m2 ->
   range (prodP (@I k)) (prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2))) ->
  eequiv P E1 c1 E2 c2 Q del ep ->
  eequiv P E1 c1 E2 c2 (Q /-\ I) del ep.
 Proof.
  intros; intros k m1 m2.
  destruct (X _ m1 m2) as [d Hd].
  exists d; intros HP.
  pose proof (le_lift_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)
   (sem_discr _ _ _) (sem_discr _ _ _) (Hd HP)) as Hd_discr.
  destruct (Hd HP); clear Hd.
  constructor; trivial; clear le_lam le_d.
  unfold prodP, andR; apply (range_discr_strengthen Hd_discr _
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)) le_r). 
  apply (range_discr_intro _ Hd_discr _
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k))).
  intros mm Hmm.
  eapply (range_discr_elim _ 
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)) (H k _ _ HP)).
  intro H'; elim Hmm.
  assert (Haux: mu ([[ c1 ]] E1 m1) (fun m =>  mem_eqU (fst mm) m) *
   mu ([[ c2 ]] E2 m2) (fun m =>  mem_eqU (snd mm) m) == 0); [ | clear H' ].
  unfold prod_distr in H'; rewrite Mlet_simpl in H'; simpl in H'.
  rewrite Umult_sym, <-(mu_stable_mult (([[ c1 ]]) E1 m1) 
   (mu ([[ c2 ]] E2 m2) (fun m =>  mem_eqU (snd mm) m))), H'.
  apply mu_stable_eq; unfold fmult; refine (ford_eq_intro _); intro m.
  rewrite Umult_sym; symmetry.
  apply (mu_stable_mult (([[ c2 ]]) E2 m2) (mem_eqU (fst mm) m)).
  symmetry; apply Ule_zero_eq;  unfold Mfst, Msnd in *.
  apply (Ueq_orc ( mu ([[ c1 ]] E1 m1) (fun m =>  mem_eqU (fst mm) m)) 0); 
   [ auto | | ]; intro Hc1.
  rewrite <-Hc1, <-le_p1, Mlet_simpl.
  apply mu_monotonic; refine (ford_le_intro _); intro m'; auto.
  rewrite (Umult_zero_simpl_right (Oeq_sym Haux) (neq_sym Hc1)).
  rewrite <-le_p2, Mlet_simpl.
  apply mu_monotonic; refine (ford_le_intro _); intro m'; auto.
 Qed.

 Lemma eequiv_range_l : forall (P Q:mem_rel) I E1 c1 E2 c2 del ep,
  (forall k (m1 m2:Mem.t k), P k m1 m2 -> range (@I k) ([[c1]] E1 m1)) ->
  eequiv P E1 c1 E2 c2 Q del ep ->
  eequiv P E1 c1 E2 c2 (Q /-\ (fun k m1 m2 => I k m1)) del ep.
 Proof.
  intros; apply eequiv_range; [ | trivial].
  intros k m1 m2 HP f Hf; simpl.
  apply (H k m1 m2 HP); intros.
  transitivity (mu ([[c2]] E2 m2) (fzero _)).
  symmetry; apply mu_zero.
  apply mu_stable_eq; refine (ford_eq_intro _); intro.
  unfold fzero; apply Hf; unfold prodP; trivial.
 Qed.

 Lemma eequiv_inv_Modify : forall (X1 X2 M1 M2:Vset.t) 
  (P Q I:mem_rel) (E1:env) (c1:cmd) (E2:env) (c2:cmd) del ep,
  (forall k, 1 <= del k)%R ->
  depend_only_rel I X1 X2 ->
  Modify E1 M1 c1 ->
  Modify E2 M2 c2 ->
  Vset.disjoint X1 M1 -> 
  Vset.disjoint X2 M2 -> 
  eequiv P E1 c1 E2 c2 Q del ep ->
  eequiv (P /-\ I) E1 c1 E2 c2 (Q /-\ I) del ep.
 Proof.
  intros.
  apply eequiv_frame; trivial.
  intros k m1 m2 HI f Hf.
  unfold prod_distr; rewrite Mlet_simpl.
  rewrite (Modify_deno_elim H1).
  rewrite <-(mu_zero ([[ c1 ]] E1 m1)); apply mu_stable_eq; 
   unfold fzero; refine (ford_eq_intro _); intro m.
  rewrite Mlet_simpl, (Modify_deno_elim H2).
  rewrite <-(mu_zero ([[ c2 ]] E2 m2)); apply mu_stable_eq; 
   unfold fzero; refine (ford_eq_intro _); intro m'.
  rewrite Munit_eq.
  apply Hf; unfold prodP; simpl.
  refine (H0 _ _ _ _ _ _ _ HI);
   apply req_mem_sym; apply req_mem_update_disjoint; trivial.
 Qed.

 Lemma eequiv_seq_weaken :
  forall E1 E2 c1 c2 c1' c2' (P:mem_rel) Q Q' lam1 ep1 lam2 ep2 lam ep,
   (forall k, 1 <= lam2 k)%R ->
   (forall k, lam1 k * lam2 k <= lam k)%R ->
   (forall k, max (ep1 k + lam1 k ** ep2 k) (ep2 k + lam2 k ** ep1 k) <= ep k) ->
   eequiv P  E1 c1  E2 c2  Q' lam1 ep1 ->
   eequiv Q' E1 c1' E2 c2' Q  lam2 ep2 ->
   eequiv P E1 (c1 ++ c1') E2 (c2 ++ c2') Q lam ep.
 Proof.
  intros.
  eapply eequiv_weaken with (P':=P) (Q':=Q) (lam':=fun k => _) (ep':=fun k => _);
   [ | | | | apply eequiv_seq with (Q':=Q')]; auto.
 Qed.

 Lemma eequiv_seq_zero: forall (P:mem_rel) E1 c1 E2 c2 Q' lam Q c1' c2' lam' lam'',
  (forall k, 1 <= lam' k)%R -> 
  (forall k, lam k * lam' k <= lam'' k)%R ->
  eequiv P E1 c1  E2 c2 Q' lam (fun _ => 0) ->
  eequiv Q' E1 c1' E2 c2' Q lam' (fun _ => 0) ->
  eequiv P E1 (c1 ++ c1') E2 (c2 ++ c2') Q lam'' (fun _ => 0).
 Proof.
  intros.
  apply eequiv_weaken with P Q (fun k => (lam k * lam' k)%R)
    (fun k => max (0 + lam k ** 0) (0 + lam' k ** 0)); trivial.
    intro k; rewrite 2 multRU_0_r, max_eq_right, 
      Uplus_zero_right; trivial.
  apply eequiv_seq with Q'; trivial.
 Qed.

 Lemma eequiv_cond_l : forall P E1 e c c' E2 c2 Q lam ep,
  eequiv (P /-\ EP1 e) E1 c E2 c2 Q lam ep ->
  eequiv (P /-\ ~- EP1 e) E1 c' E2 c2 Q lam ep ->
  eequiv P E1 [If e then c else c'] E2 c2 Q lam ep.
 Proof.
  unfold eequiv, andR, notR, EP1, is_true.
  intros P E3 e1 c c' E4 c2 Q lam ep Ht Hf k m1 m2.
  case_eq (E.eval_expr e1 m1); intro Heq.
  destruct (Ht _ m1 m2) as (dt,Hdt).
  exists dt; intro Hm.
  rewrite deno_cond, Heq; auto.

  destruct (Hf _ m1 m2) as (df,Hdf). 
  exists df; intro Hm. 
  rewrite deno_cond, Heq; auto.
  apply Hdf; split; trivial.
  apply not_is_true_false; trivial.
 Qed.

 Lemma eequiv_cond_r : forall P E1 c1 E2 e c c' Q lam ep,
  eequiv (P /-\ EP2 e) E1 c1 E2 c Q lam ep ->
  eequiv (P /-\ ~- EP2 e) E1 c1 E2 c' Q lam ep ->
  eequiv P E1 c1 E2 [If e then c else c'] Q lam ep.
 Proof.
  unfold eequiv, andR, notR, EP2, is_true.
  intros P E3 c c' e E4 c2 Q lam ep Ht Hf k m1 m2.
  case_eq (E.eval_expr e m2); intro Heq.
  destruct (Ht _ m1 m2) as (dt,Hdt).
  exists dt; intro Hm; rewrite deno_cond, Heq; auto.
  destruct (Hf _ m1 m2) as (df,Hdf).
  exists df; intro Hm. rewrite deno_cond, Heq.
  apply Hdf; rewrite Heq; auto using diff_false_true.
 Qed.

 Lemma eequiv_cond : 
  forall P Q E1 (e1:E.expr T.Bool) c1 c2 E2 (e2:E.expr T.Bool) c3 c4 lam ep,
   (forall k, 1 <= lam k)%R ->
   eequiv (P /-\ (EP1 e1 /-\ EP2 e2)) E1 c1 E2 c3 Q lam ep ->
   eequiv (P /-\ (~- EP1 e1 /-\ ~- EP2 e2)) E1 c2 E2 c4 Q lam ep ->
   (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
   eequiv P E1 [If e1 then c1 else c2] E2 [If e2 then c3 else c4] Q lam ep.
 Proof.
  intros; apply eequiv_cond_l; apply eequiv_cond_r.
  eapply eequiv_weaken with (5:=X); auto with real; simplMR; trivial.
  apply eequiv_weaken with falseR Q (fun _ => R1) (fzero _); auto; unfold EP1, EP2.
  intros k m1 m2 ((H2, H3), H4); apply H4; erewrite <-H0; eauto. 
  apply eequiv_weaken with falseR Q  (fun _ => R1) (fzero _); 
   auto; unfold EP1, EP2.
  intros k m1 m2 ((H2, H3), H4); apply H3; erewrite H0; eauto.
  eapply eequiv_weaken with (5:=X0); auto; simplMR; trivial.
 Qed.

 Lemma eequiv_assign_l : forall Q E1 E2 t1 (x1:Var.var t1) e1,
  eequiv (upd1 Q x1 e1) E1 [x1 <- e1] E2 nil Q (fun _ => R1) (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (Munit (m1{!x1<--E.eval_expr e1 m1!}, m2)); intros.
  rewrite deno_assign; rewrite deno_nil. 
  apply le_lift_Munit; trivial.
 Qed.

 Lemma eequiv_assign_r : forall Q E1 E2 t2 (x2:Var.var t2) e2,
  eequiv (upd2 Q x2 e2) E1 nil E2 [x2 <- e2] Q (fun _ => R1) (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (Munit (m1, m2{!x2<--E.eval_expr e2 m2!})); intros.
  rewrite deno_assign; rewrite deno_nil.
  apply le_lift_Munit; trivial.
 Qed.
 
 Lemma eequiv_assign : forall Q E1 E2 t1 (x1:Var.var t1) t2 (x2:Var.var t2) e1 e2, 
  eequiv (upd_para Q x1 e1 x2 e2) E1 [x1 <- e1] E2 [x2 <- e2] Q 
  (fun _ => R1) (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (Munit (m1{!x1<-- E.eval_expr e1 m1!}, m2{!x2<--E.eval_expr e2 m2!})).
  intros; repeat rewrite deno_assign.
  apply le_lift_Munit; trivial.
 Qed.

 Lemma eequiv_random_lift : forall (P Q:mem_rel) E1 E2 t1 t2 (x1:Var.var t1) 
  (x2:Var.var t2) (d1:DE.support t1) (d2:DE.support t2) lam ep,
  (forall k (m1 m2:Mem.t k), sig (fun d => P _ m1 m2 -> 
   le_lift (fun v1 v2 => Q _ (m1 {!x1 <-- v1!}) (m2 {!x2 <-- v2!})) 
   d (DE.eval_support d1 m1)
   (DE.eval_support d2 m2) (lam k) (ep k))) ->
  eequiv P E1 [x1 <$- d1] E2 [x2 <$- d2] Q lam ep.
 Proof.
  unfold eequiv; intros.
  destruct (X _ m1 m2) as (d,Hd); clear X.
  exists (Mlet d 
   (fun v12 => Munit ((m1 {!x1 <-- fst v12!}),(m2 {!x2 <-- snd v12!})))).
  intros Hm; repeat rewrite deno_random.
  apply le_lift_weaken with 
   (@Q k) (lam k * R1)%R (max (ep k + (lam k) ** 0) (0 + R1 ** ep k)).
  trivial.
  rewrite Rmult_1_r; auto.
  apply max_le; [ rewrite multRU_0_r | rewrite multRU_1_l]; auto.
  refine (le_lift_Mlet _ _ _ _ 
   (cover_eq_prod _ _ (carT_cover _ _) (carT_cover _ _)) _ (Rle_refl _) (Hd Hm) _).
  refine (le_lift_discr_witness _ _  (carT_cover _ _) (carT_cover _ _) 
   (DE.discrete_support _ _) (DE.discrete_support _ _) (Hd Hm)).
  intros; apply le_lift_Munit; trivial.
 Qed.

  Lemma eequiv_random_discr: forall (P:mem_rel) E1 E2 t (x1:Var.var t) 
   (x2:Var.var t) (d1:DE.support t) (d2:DE.support t) lam (ep:nat -o> U),
   (forall k, 1 <= lam k)%R ->
   (forall k (m1 m2:Mem.t k), P k m1 m2 ->
     le_dist (DE.eval_support d1 m1) (DE.eval_support d2 m2) (lam k) (ep k)) ->
   eequiv P E1 [x1 <$- d1] E2 [x2 <$- d2] (EP_eq_expr x1 x2) lam ep.
  Proof.
   intros.
   apply eequiv_random_lift. 
   intros k m1 m2.
   set (p := parity_split (D_points (DE.discrete_support d1 m1))
    (D_points (DE.discrete_support d2 m2))).
   set (d' := Mlet (dmin (carT k t) (carT_cover k t) p
    (DE.eval_support d1 m1) (DE.eval_support d2 m2)) (fun a => Munit (a, a))).
   exists d'; intros Hm.
   eapply le_lift_weaken; 
    [ | | | apply (@le_lift_eq_intro _ _ (carT_cover k t) _ _
     (DE.discrete_support d1 m1) (DE.discrete_support d2 m2) 
     (lam k) (ep k) (H k)) ]; auto.
   intros; unfold EP_eq_expr; simpl; subst; rewrite 2 Mem.get_upd_same; trivial.
  Qed.

 
 Fixpoint sum_powR (lam:R) (ep:U) (n:nat) : U :=
  match n with
   | 0%nat => 0 
   | S n' => ep + lam ** (sum_powR lam ep n')
  end.

 Import Rpow_def.

 Fixpoint sum_powR' (lam:R) (ep:U) (n:nat) : U :=
  match n with
   | 0%nat => 0 
   | S n' => 
    max (ep + lam ** (sum_powR' lam ep n')) 
        ((sum_powR' lam ep n') + pow lam n' ** ep)
  end.

 Lemma sum_powR_powR' : forall n lam ep, 
  (1 <= lam)%R ->
  sum_powR' lam ep n <= sum_powR lam ep n.
 Proof.
  induction n; intros; simpl.
  trivial.
  
  apply max_le.
  apply Uplus_le_compat_right.
  apply multRU_le_compat; auto.
  fourier.
 
  rewrite IHn; trivial.
  
  clear IHn.
  induction n; intros; simpl; repeat Usimpl.
  rewrite multRU_1_l, multRU_0_r; trivial.
 
  rewrite <-Uplus_assoc; apply Uplus_le_compat_right.
  transitivity (lam ** (sum_powR lam ep n + lam ^ n ** ep));
   [ | apply multRU_le_compat; auto with real; fourier].

  rewrite <-multRU_distr_plus_l; trivial.
  apply Uplus_le_compat_right.
  rewrite <-Rmult_multRU_assoc; [ | | apply pow_R1_Rle]; trivial.
 Qed.

 Lemma eequiv_nwhile_cte : forall (P:mem_rel) E1 
  (e1:E.expr T.Bool) c1 E2 (e2:E.expr T.Bool) c2 lam ep n,
  (forall k, 1 <= lam k)%R ->
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
  eequiv (P /-\ EP1 e1 /-\ EP2 e2) E1 c1 E2 c2 P lam ep -> 
  eequiv P E1 (unroll_while e1 c1 n) E2 (unroll_while e2 c2 n) P
  (fun k => pow (lam k) n) (fun k => sum_powR (lam k) (ep k) n).
 Proof.
  intros I E1 e1 c1 E2 e2 c2 lam ep n Hlam I_e Hc.
  apply eequiv_weaken with I I (fun k : nat => lam k ^ n)%R
    (fun k : nat => sum_powR' (lam k) (ep k) n); auto using sum_powR_powR'.

  induction n; simpl.
  (* base case *)
  refine (eequiv_cond _ _ _ I_e).
  intros _; auto with real.
  eapply eequiv_weaken; 
   [  rewrite proj1_MR | | | | apply eequiv_nil with (P:=I) ]; auto.
  eapply eequiv_weaken; 
   [  rewrite proj1_MR | | | | apply eequiv_nil with (P:=I) ]; auto.

  (* inductive case *)
  refine (eequiv_cond _ _ _ I_e).
 
  intro; rewrite <-(Rmult_1_l 1%R); apply Rmult_le_compat; trivial; try fourier.
  apply pow_R1_Rle; trivial.

  apply eequiv_seq with I; trivial. 
  intros; apply pow_R1_Rle; trivial.

  eapply eequiv_weaken with I I (fun _ => R1) (fzero _);
   [  rewrite proj1_MR | | | | ]; auto.

  intro; rewrite <-(Rmult_1_l 1%R); apply Rmult_le_compat; trivial; try fourier.
  apply pow_R1_Rle; trivial.

  apply eequiv_nil.
 Qed.


 Section nWHILE.

  Variables c1 c2 : cmd.

  Variables e1 e2 : env.

  Variable I : mem_rel.

  Variables b1 b2 : E.expr T.Bool.

  Variable k : nat.

  Variable ep : U.
 
  Variable lam : R.

  Hypothesis H_lam : (1 <= lam)%R.
 
  Variable q : nat.

  Hypothesis Hc: forall m1 m2 : Mem.t k, 
   sig (fun d =>
    (I /-\ EP1 b1 /-\ EP2 b2) _ m1 m2 ->
    le_lift 
    ((I /-\ EP_eq_expr b1 b2) k) d 
    (([[ c1 ]]) e1 m1) (([[ c2 ]]) e2 m2) 
    lam ep).

  Lemma nwhile_le_lift : forall m1 m2 : Mem.t k,
   sig (fun d' => (I /-\ EP_eq_expr b1 b2) _ m1 m2 ->
    le_lift ((I /-\ ~- EP1 b1 /-\ ~- EP2 b2) k) d' 
    (drestr ([[ unroll_while b1 c1 q ]] e1 m1) (negP (EP k b1))) 
    (drestr ([[ unroll_while b2 c2 q ]] e2 m2) (negP (EP k b2)))
    (pow lam q) (sum_powR lam ep q)).
  Proof.
   cut (forall m1 m2 : Mem.t k, sig (fun d' => (I /-\ EP_eq_expr b1 b2) _ m1 m2 ->
    le_lift ((I /-\ ~- EP1 b1 /-\ ~- EP2 b2) k) d'
    (drestr ([[ unroll_while b1 c1 q ]] e1 m1) (negP (EP k b1))) 
    (drestr ([[ unroll_while b2 c2 q ]] e2 m2) (negP (EP k b2)))
    (pow lam q) (sum_powR' lam ep q))).
   intros H m1 m2; destruct (H m1 m2) as (d',Hd'); clear H.
   exists d'; intro Hm.
   apply le_lift_weaken with (4:=Hd' Hm); auto using sum_powR_powR'.
   unfold EP_eq_expr; induction q; intros m1 m2.
   (* base case *)
   case_eq (E.eval_expr b1 m1); intro Heq.
   (* case [b1] *)
   exists (distr0 _); intros (H1m, H2m).
   rewrite (eq_distr_intro _ (Munit m1) (unroll_while_0_elim e1 b1 c1 m1)),
    (eq_distr_intro _ (Munit m2) (unroll_while_0_elim e2 b2 c2 m2)).
   unfold drestr, negP, negb, EP; rewrite 2 Mlet_unit, <-H2m, Heq.
   eapply le_lift_eq_compat; [ apply Oeq_refl |  | | | | apply le_lift_prod ];
    auto.
   (* case [~b1] *)
   exists (Munit (m1, m2)); intros (H1m, H2m).
   rewrite (eq_distr_intro _ (Munit m1) (unroll_while_0_elim e1 b1 c1 m1)),
    (eq_distr_intro _ (Munit m2) (unroll_while_0_elim e2 b2 c2 m2)).
   unfold drestr, negP, negb, EP; rewrite 2 Mlet_unit, <-H2m, Heq.
   apply le_lift_Munit.
   trivial.
   unfold EP1, EP2, notR; repeat split; [ trivial | | rewrite <-H2m ];
    apply (proj2 (not_true_iff_false _) Heq).
   (* inductive case *)
   case_eq (E.eval_expr b1 m1); intro Heq.
   (* case [b1] *)
   destruct (Hc m1 m2) as (d',Hd'); clear Hc.
   exists (Mlet d' 
    (fun mm => proj1_sig (IHn (fst mm) (snd mm)))); intros (H1m,H2m).
   simpl; rewrite deno_cond, deno_cond, <-H2m, Heq.
   unfold drestr; repeat rewrite deno_app, (Mcomp _ _ _).
   apply le_lift_Mlet with 
    ((I /-\ (EP_eq_expr b1 b2)) k)
    (fun ab ab' => mem_eqU (fst ab) (fst ab') * mem_eqU (snd ab) (snd ab')).
   apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
   refine (le_lift_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) 
    (sem_discr _ _ _) (sem_discr _ _ _) (Hd' _)); 
   repeat split; [ trivial | | unfold EP2; rewrite <-H2m ]; apply Heq.
   apply pow_R1_Rle; trivial.
   apply Hd'. 
   repeat split; [ trivial | | unfold EP2; rewrite <-H2m ]; apply Heq.
   intros m1' m2' Hm'; unfold fst, snd.
   destruct (IHn m1' m2') as (dn,Hdn); auto.
   (* case [~b1] *)
   exists (Munit (m1,m2)); intros (H1m, H2m).
   simpl; rewrite deno_cond, deno_cond, <-H2m, Heq.
   unfold drestr, negP, negb, EP.
   rewrite deno_nil, deno_nil, Mlet_unit, Mlet_unit, <-H2m, Heq.
   eapply le_lift_weaken; [  intros ? ? H'; apply H' | | | 
    apply le_lift_Munit ]; trivial.
   rewrite <-(Rmult_1_l 1%R); apply Rmult_le_compat; try fourier.
   apply pow_R1_Rle; trivial.
   unfold EP1, EP2, notR; repeat split; [ trivial | | rewrite <-H2m ];
    apply (proj2 (not_true_iff_false _) Heq).
  Qed.
 
 End nWHILE.


 Lemma eequiv_while : forall (P P':mem_rel) E1 (e1:E.expr T.Bool) c1 E2 
  (e2:E.expr T.Bool) c2 lam ep q,
  implMR P' P ->
  (forall k, 1 <= lam k)%R ->
  (forall k (m1 m2:Mem.t k),  (P' /-\ EP_eq_expr e1 e2) _ m1 m2 -> 
   [[ [while e1 do c1] ]] E1 m1 == 
   drestr ([[ unroll_while e1 c1 (q k) ]] E1 m1) (negP (@EP k e1)) /\
   [[ [while e2 do c2] ]] E2 m2 == 
   drestr ([[ unroll_while e2 c2 (q k) ]] E2 m2) (negP (@EP k e2))) ->
  eequiv (P /-\ EP1 e1 /-\ EP2 e2) E1 c1 E2 c2 (P /-\ EP_eq_expr e1 e2) lam ep -> 
  eequiv (P' /-\ EP_eq_expr e1 e2) 
  E1 [while e1 do c1] 
  E2 [while e2 do c2] 
  (P /-\ ~-EP1 e1 /-\ ~-EP2 e2) 
  (fun k => pow (lam k) (q k))
  (fun k => sum_powR (lam k) (ep k) (q k)).
 Proof.
  unfold eequiv; intros.  
  destruct (nwhile_le_lift (H0 k) (q k) (X k) m1 m2) as (d,Hd).
  exists d; intro Hm.
  apply le_lift_eq_compat with 
   (6:=Hd (andR_impl_morph H (implMR_refl (EP_eq_expr e1 e2)) Hm)); trivial.
  symmetry; apply (proj1 (H1 _ _ _ Hm)).
  symmetry; apply (proj2 (H1 _ _ _ Hm)).
 Qed.

 (* ProdRR f i 0      = 1                          *)
 (* ProdRR f i (S n)  = (f i) x ... x (f (i + n))  *)
 Fixpoint ProdRR (f:nat -> R) i (n:nat) {struct n} : R :=
  match n with 
   | O => 1%R
   | S n' => (f i * ProdRR f (S i) n')%R
  end.

 Fixpoint sum_powR2' (lam:nat -> R) (ep:nat -> U) (i:nat) (n:nat) {struct n} : U :=
  match n with
   | O => 0 
   | S n' => max
    (ep i + lam i ** sum_powR2' lam ep  (S i) n')
    (sum_powR2' lam ep (S i) n' + ProdRR lam (S i) n' ** ep i)
  end.

 Lemma ProdRR_ge_1 : forall f n i,
  (forall k, (k < n)%nat -> (1 <= f (i + k)%nat)%R) ->
  (1 <= ProdRR f i n)%R.
 Proof.
  induction n; intros.
  trivial.
  simpl.
  rewrite <-(Rmult_1_l 1%R), <-(plus_0_r i).
  apply Rmult_le_compat; auto with real.
  apply H; omega.
  apply IHn; intros.
  rewrite plus_Snm_nSm.
  rewrite plus_0_r.
  apply H; omega.
 Qed.

 Lemma ProdRR_S : forall f b a,
  ProdRR f a (S b) = (ProdRR f a b * f (a + b)%nat)%R.
 Proof. 
  induction b; intros.
  simpl; rewrite Rmult_1_l, Rmult_1_r, plus_0_r; trivial. 
  change (ProdRR f a (S (S b))) with (f a * ProdRR f (S a) (S b))%R.
  rewrite IHb; simpl.
  rewrite Rmult_assoc.
  apply f_equal, f_equal, f_equal; omega.
 Qed.

 Lemma ProdRR_ge_1_monotonic : forall (f:nat -> R) (a N1 N2:nat),
  (forall k, (a <= k < a + N2)%nat -> (1 <= f k)%R) ->
  (N1 <= N2)%nat -> (ProdRR f a N1 <= ProdRR f a N2)%R.
 Proof.
  induction N2; intros H Hle.
  inversion Hle; trivial.
  inversion Hle; subst; [trivial | ].
  rewrite ProdRR_S, IHN2; [ | | trivial].
  rewrite <-Rmult_1_r at 1; apply Rmult_le_compat; [ | fourier | trivial | ].
  rewrite <-ProdRR_ge_1; [fourier | intros; apply H; omega].
  apply H; omega.
  intros; apply H; omega.
 Qed.

 Lemma ProdRR_exp : forall f b,
  ProdRR (fun k => exp (f k)) 0 (S b) = exp (sum_f_R0 f b).
 Proof.
  induction b; intros.
  simpl; rewrite Rmult_1_r; trivial.
  simpl sum_f_R0; rewrite exp_plus, <-IHb.
  rewrite ProdRR_S, plus_0_l; trivial.
 Qed.


 Section nWHILE_GEN.

  Variables c1 c2 : cmd.
 
  Variables e1 e2 : env.

  Variables I : mem_rel.
 
  Variables b1 b2 : E.expr T.Bool.
 
  Variable i : Var.var T.Nat.

  Variable HI : implMR I (EP_eq_expr b1 b2).

  Variable k : nat.

  Variable ep : nat -o> U.

  Variable lam : nat -> R.

  Hypothesis H_lam : forall k, (1 <= lam k)%R. 

  Hypothesis Hd : forall (m1 m2 : Mem.t k),  
   sig (fun d =>
    (I /-\ EP1 b1 /-\ EP2 b2) _ m1 m2 ->
    le_lift 
    ((I /-\ (fun k (m1' m2':Mem.t k) => m1' i = S (m1 i))) k) 
    d  
    (([[ c1 ]]) e1 m1) 
    (([[ c2 ]]) e2 m2) 
    (lam (m1 i)) (ep (m1 i))).
  
  Lemma nwhile_le_lift' : forall n (m1 m2 : Mem.t k), sig (fun d' => 
   I m1 m2 ->
   le_lift ((I /-\ ~- EP1 b1 /-\ ~- EP2 b2) k) d'
   (drestr ([[ unroll_while b1 c1 n ]] e1 m1) (negP (EP k b1))) 
   (drestr ([[ unroll_while b2 c2 n ]] e2 m2) (negP (EP k b2)))
   (ProdRR lam (m1 i) n) (sum_powR2' lam ep (m1 i) n)).
  Proof.
   unfold EP_eq_expr in *.
   induction n; intros m1 m2.
   (* base case *)
   case_eq (E.eval_expr b1 m1); intro Heq.
   (* case [b1] *)
   exists (distr0 _); intro Hm.
   rewrite (eq_distr_intro _ (Munit m1) (unroll_while_0_elim e1 b1 c1 m1)),
    (eq_distr_intro _ (Munit m2) (unroll_while_0_elim e2 b2 c2 m2)).
   unfold drestr, negP, negb, EP; rewrite 2 Mlet_unit, <-(HI Hm), Heq.
   eapply le_lift_eq_compat; 
    [ apply Oeq_refl |  | | | | apply le_lift_prod ]; auto.
   (* case [~b1] *)
   exists (Munit (m1, m2)); intro Hm.
   rewrite (eq_distr_intro _ (Munit m1) (unroll_while_0_elim e1 b1 c1 m1)),
    (eq_distr_intro _ (Munit m2) (unroll_while_0_elim e2 b2 c2 m2)).
   unfold drestr, negP, negb, EP; rewrite 2 Mlet_unit, <-(HI Hm), Heq.
   apply le_lift_Munit.
   trivial.
   unfold EP1, EP2, notR; repeat split; [ trivial | | rewrite <-(HI Hm) ];
    apply (proj2 (not_true_iff_false _) Heq).
   
   (* inductive case *)
   case_eq (E.eval_expr b1 m1); intro Heq.
   (* case [b1] *)
   destruct (Hd m1 m2) as (d',Hd'); clear Hd.
   exists (Mlet d' (fun mm => proj1_sig (IHn (fst mm) (snd mm)))); intro Hm.
   simpl; rewrite deno_cond, deno_cond, <-(HI Hm), Heq.
   unfold drestr; repeat rewrite deno_app, (Mcomp _ _ _).
   apply le_lift_Mlet with 
    ((I /-\ (fun (k0 : nat) (m1' _ : Mem.t k0) => m1' i = S (m1 i))) k)
    (fun ab ab' => mem_eqU (fst ab) (fst ab') * mem_eqU (snd ab) (snd ab')).
   apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
   refine (le_lift_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) 
    (sem_discr _ _ _) (sem_discr _ _ _) (Hd' _));
   repeat split; [ trivial | unfold EP1 | unfold EP2; rewrite <-(HI Hm) ]; trivial.
   apply ProdRR_ge_1; trivial.
   apply Hd'. 
   repeat split; [ trivial | | unfold EP2; rewrite <-(HI Hm) ]; apply Heq.
   intros m1' m2' (H1m',Hi_m1'); unfold fst, snd.
   rewrite <-Hi_m1'; destruct (IHn m1' m2'); auto.
   (* case [~b1] *)
   exists (Munit (m1,m2)); intro Hm.
   simpl; rewrite deno_cond, deno_cond, <-(HI Hm), Heq.
   unfold drestr, negP, negb, EP.
   rewrite deno_nil, deno_nil, Mlet_unit, Mlet_unit, <-(HI Hm), Heq.
   eapply le_lift_weaken with  (P':=(I /-\ ~- EP1 b1  /-\ ~- EP2 b2) k) 
    (lam' := (lam (m1 i) * ProdRR lam (S (m1 i)) n)%R); 
    [ | | | apply le_lift_Munit ]; trivial.
   rewrite <-(Rmult_1_l 1%R).
   apply Rmult_le_compat; trivial; try fourier.
   apply ProdRR_ge_1; trivial.
   unfold EP1, EP2, notR; repeat split; [ trivial | | rewrite <-(HI Hm) ];
    apply (proj2 (not_true_iff_false _) Heq).
  Qed.

 End nWHILE_GEN.


 Lemma eequiv_while' : 
  forall (P:mem_rel) E1 (e1:E.expr T.Bool) c1 E2 (e2:E.expr T.Bool) c2 
   (i:Var.var T.Nat) (lam:nat -> nat -> R)  (ep:nat -> nat -> U) (q: nat -> nat),
   (forall k1 k2, 1 <= lam k1 k2)%R ->
   implMR P (EP_eq_expr e1 e2) ->
   (forall k (m1 m2:Mem.t k),  P _ m1 m2 -> 
    [[ [while e1 do c1] ]] E1 m1 == 
    drestr ([[ unroll_while e1 c1 (q k) ]] E1 m1) (negP (@EP k e1)) /\
    [[ [while e2 do c2] ]] E2 m2 == 
    drestr ([[ unroll_while e2 c2 (q k) ]] E2 m2) (negP (@EP k e2))) ->
  (forall (n:nat -> nat), 
   eequiv 
   (P /-\ EP1 e1 /-\ EP2 e2 /-\ (fun k (m1 _:Mem.t k) => m1 i = n k)) 
   E1 c1 E2 c2 
   (P /-\ (fun k (m1 _:Mem.t k) => m1 i = S (n k))) 
   (fun k => lam k (n k)) (fun k => ep k (n k))) ->
  forall (i0:nat -> nat), 
   eequiv (P /-\ (fun k (m1 _:Mem.t k) => m1 i = i0 k)) 
   E1 [while e1 do c1] E2 [while e2 do c2] 
   (P /-\ ~-EP1 e1 /-\ ~-EP2 e2)
   (fun k => ProdRR (lam k) (i0 k) (q k)) 
   (fun k => sum_powR2' (lam k) (ep k) (i0 k) (q k)).
 Proof.
  unfold eequiv; intros.
  destruct (fun H'' => 
   @nwhile_le_lift' c1 c2 E1 E2 P e1 e2 i H0 k (ep k) (lam k) (H k)  
   H'' (q k) m1 m2) as (dn, Hdn).
  intros m1' m2'.
  destruct (X (fun k => m1' i) _ m1' m2') as (d,Hd); clear X H0.
  exists d; intros (?,(?,?)).
  eapply le_lift_weaken; [ | | | apply Hd ]; trivial.
  repeat split; trivial.
  exists dn; intros (H1m, H2m).
  eapply le_lift_weaken; [  intros ? ? Hm'; apply Hm' | 
   rewrite <-H2m | rewrite <-H2m; apply Ole_refl | ]; trivial.
  eapply le_lift_eq_compat; [ | | | | | apply (Hdn H1m) ]; trivial.
  symmetry; apply (proj1 (H1 _ _ _ H1m)).
  symmetry; apply (proj2 (H1 _ _ _ H1m)).
 Qed.

 Lemma equiv_seq_eequiv : forall E1 c1 c1' E2 c2 c2' P Q' Q lam ep,
  (forall k : nat, (1 <= lam k)%R) ->
  equiv P  E1 c1  E2 c2  Q' ->
  eequiv Q' E1 c1' E2 c2' Q lam ep ->
  eequiv P E1 (c1++c1') E2 (c2++c2') Q lam ep.
 Proof.
  intros.
  eapply eequiv_weaken with (P':=P) (Q':=Q); 
   [ | | | | eapply eequiv_seq with  (lam := fun _ => R1) 
    (ep:= fun _ => D0) (lam':= lam) (ep' := ep) (Q':= Q') ]; trivial.
  auto with real. 
  simpl; intro; repeat multRU_simpl; repeat Usimpl; auto.
  apply (equiv_eequiv H0).
 Qed.

 Lemma eequiv_seq_equiv : forall E1 c1 c1' E2 c2 c2' P Q' Q lam ep,
  (forall k : nat, (1 <= lam k)%R) ->
  eequiv P  E1 c1  E2 c2  Q' lam ep ->
  equiv  Q' E1 c1' E2 c2' Q ->
  eequiv P  E1 (c1++c1') E2 (c2++c2') Q lam ep.
 Proof.
  intros.
  eapply eequiv_weaken with (P':=P) (Q':=Q); 
   [ | | | | eapply eequiv_seq with  (lam' := fun _ => R1) 
    (ep':= fun _ => D0) (lam:= lam) (ep := ep) (Q':= Q') ]; trivial.
  auto with real. 
  simpl; intro; repeat multRU_simpl; repeat Usimpl; auto.
  apply (equiv_eequiv H0).
 Qed.

 Lemma eequiv_cons_equiv :forall E1 E2 (i1 i2:I.instr) (c1 c2:cmd)  
  (P Q' Q : mem_rel) (lam:nat -> R) (ep:nat -o> U),
  (forall k : nat, (1 <= lam k)%R) ->
  equiv P E1 [i1] E2 [i2] Q' ->
  eequiv Q' E1 c1 E2 c2 Q lam ep ->
  eequiv P E1 (i1:: c1) E2 (i2::c2) Q lam ep.
 Proof.
  intros.
  change  (eequiv P E1 ([i1] ++ c1) E2 ([i2] ++ c2) Q lam ep).
  apply equiv_seq_eequiv with Q'; trivial.
 Qed.

 Lemma equiv_cons_eequiv :forall E1 E2 (i1 i2:I.instr) (c1 c2:cmd)  
  (P Q' Q : mem_rel) (lam:nat -> R) (ep:nat -o> U),
  (forall k : nat, (1 <= lam k)%R) ->
  eequiv P E1 [i1] E2 [i2] Q' lam ep ->
  equiv Q' E1 c1 E2 c2 Q ->
  eequiv P E1 (i1:: c1) E2 (i2::c2) Q lam ep.
 Proof.
  intros.
  change  (eequiv P E1 ([i1] ++ c1) E2 ([i2] ++ c2) Q lam ep).
  apply eequiv_seq_equiv with Q'; trivial.
 Qed.

 Lemma assert_assign_comm : forall E1 E2 t 
  (x1 x2:Var.var t) e1 e2 b1 b2 (P Q:mem_rel),
  (forall k (m1 m2: Mem.t k), 
   P _ m1 m2 ->
   @E.eval_expr k T.Bool b1 (m1 {!x1 <-- E.eval_expr e1 m1!}) = 
   E.eval_expr b2 m2 /\
   Q _ (m1 {!x1 <-- E.eval_expr e1 m1!}) (m2 {!x2 <-- E.eval_expr e2 m2!})) ->
  eequiv P 
  E1 [ x1 <- e1; Assert b1] 
  E2 [ Assert b2; x2 <- e2 ] 
  Q (fun _ => R1) (fzero _).
 Proof.
  intros; intros k m1 m2.
  exists  (if @E.eval_expr k T.Bool b1 (m1 {!x1 <-- E.eval_expr e1 m1!}) then
   Munit (m1 {!x1 <-- E.eval_expr e1 m1!},m2 {!x2 <-- E.eval_expr e2 m2!}) 
   else distr0 _); intro Hm.
  rewrite (deno_cons _ (_ <- _) [Assert _]),
   (deno_cons _ (Assert _) [_ <- _]), deno_assign, 
   deno_assert, Mlet_unit, deno_assert. 
  repeat setoid_rewrite (proj1 (H _ _ _ Hm)).
  case (E.eval_expr b2 m2).
  rewrite Mlet_unit, deno_assign.
  apply (le_lift_Munit _ _ _ (Rle_refl _) (proj2 (H _ _ _ Hm))).
  rewrite Mlet_distr0_abs.
  apply (le_lift_distr0 _ _ (Rle_refl _)).
 Qed.
 
 Lemma eequiv_trans_l : forall (P1 P2 Q1 Q2 Q3:mem_rel) 
  E1 c1 E2 c2 E3 c3 ep1 ep2 lam1 lam2 ep lam,
  (forall k, 1 <= lam1 k)%R ->
  (forall k, 1 <= lam2 k)%R ->
  (forall k, lam1 k * lam2 k <= lam k)%R ->
  (forall k, max (ep1 k + lam1 k ** ep2 k) (ep2 k + lam2 k ** ep1 k) <= ep k) ->
  decMR P2 ->
  refl_supMR2 P2 P1 ->
  (forall k x y z, Q1 k x y -> Q2 k y z -> Q3 k x z) -> 
  eequiv P1 E1 c1 E2 c2 Q1 lam1 ep1 -> 
  eequiv P2 E2 c2 E3 c3 Q2 lam2 ep2 ->
  eequiv P2 E1 c1 E3 c3 Q3 lam ep.
 Proof.
  unfold eequiv; intros. 
  destruct (X0 _ m1 m1) as (d, Hd); destruct (X1 _ m1 m2) as (d',Hd').
  destruct (X _ m1 m2).
  exists (@dd' _ _ _ (@mem_eqU k) 
   (Q1 k) (Q2 k) d d' 
   (ep1 k) (ep2 k) (lam1 k) (lam2 k) 
   (@deno k c1 E1 m1) (@deno k c2 E2 m1) (@deno k c3 E3 m2) 
   (Hd (H3 k m1 m2 p))
   (Hd' p)).
  intros _.
  eapply le_lift_weaken; [ | | | 
    apply (le_lift_trans_discr _ _ _ (@mem_eqU_spec k)
   (@mem_eqU_spec k) (@mem_eqU_spec k) (@Q3 k) (@H4 k) (Hd (H3 _ _ _ p))
   (Hd' p) (sem_discr _ _ _) (sem_discr _ _ _) (sem_discr _ _ _)) ]; auto.
  exists (distr0 _).
  intro; contradiction.
 Qed.

 Lemma eequiv_trans_r : forall (P1 P2 Q1 Q2 Q3:mem_rel) 
  E1 c1 E2 c2 E3 c3 ep1 ep2 lam1 lam2 ep lam,
  (forall k, 1 <= lam1 k)%R ->
  (forall k, 1 <= lam2 k)%R ->
  (forall k, lam2 k * lam1 k <= lam k)%R ->
  (forall k, max (ep1 k + lam1 k ** ep2 k) (ep2 k + lam2 k ** ep1 k) <= ep k) ->
  decMR P1 ->
  refl_supMR2 (transpR P1) (transpR P2) ->
  (forall k x y z, Q1 k x y -> Q2 k y z -> Q3 k x z) -> 
  eequiv P1 E1 c1 E2 c2 Q1 lam1 ep1 -> 
  eequiv P2 E2 c2 E3 c3 Q2 lam2 ep2 ->
  eequiv P1 E1 c1 E3 c3 Q3 lam ep.
 Proof.
  intros; apply eequiv_transp.
  eapply eequiv_trans_l with (P1:=transpR P2) (P2:=transpR P1)
   (Q1:=transpR Q2) (Q2:=transpR Q1) (E2:=E2) (c2:=c2)
   (lam1:=lam2) (lam2:=lam1) (ep1:=ep2) (ep2:=ep1); auto.
  intros; rewrite max_comm; trivial.
  unfold transpR; intros; trivial.  
  apply H4 with y; trivial.
  apply eequiv_transp.
  eapply eequiv_weaken with (P':=P2) (Q':=Q2) (lam':=lam2) (ep':=ep2); trivial.
  rewrite transpR_transpR; trivial.
  rewrite transpR_transpR; trivial.
  apply eequiv_transp.
  eapply eequiv_weaken with (P':=P1) (Q':=Q1) (lam':=lam1) (ep':=ep1); trivial.
  rewrite transpR_transpR; trivial.
  rewrite transpR_transpR; trivial.
 Qed.


 Section RANDOM_ASSERT.

  Variable Uleb : U -> U -> bool.
 
  Hypothesis Uleb_spec1 : forall x y : U, x <= y -> Uleb x y.

  Hypothesis Uleb_spec2 : forall x y : U, y < x -> Uleb x y = false.
  
  Variable E1 E2 : env.

  Variable t : T.type.

  Variables d1 d2 : DE.support t.

  Variable P : mem_rel.

  Variable F : forall k, T.interp k t -> U.

  Variables e1 e2 : E.expr T.Bool.
 
  Variables x1 x2 : Var.var t.

  Variable lam : nat -> R.

  Variable ep : nat -o> U.

  Let d1i k (m:Mem.t k) := DE.eval_support d1 m. 
 
  Let d2i k (m:Mem.t k) := DE.eval_support d2 m. 
 
  Let d1i' k (m:Mem.t k) := 
   drestr (DE.eval_support d1 m) (fun v => E.eval_expr e1 (m{!x1 <-- v!})). 
  
  Let d2i' k (m:Mem.t k) :=
   drestr (DE.eval_support d2 m) (fun v => E.eval_expr e2 (m{!x2 <-- v!})). 

  Lemma d1'_discr: forall k (m:Mem.t k), is_Discrete (d1i' m).
  Proof.
   intros; apply (is_Discrete_Mlet _ (DE.discrete_support _ _)).
   intros a; case (E.eval_expr e1 (m {!x1 <-- a!}));
    [ apply is_Discrete_Munit | apply (is_Discrete_distr0 (T.default k t)) ].
  Defined.

  Lemma d2'_discr: forall k (m:Mem.t k), is_Discrete (d2i' m).
  Proof.
   intros; apply (is_Discrete_Mlet _ (DE.discrete_support _ _)).
   intros a; case (E.eval_expr e2 (m {!x2 <-- a!}));
    [ apply is_Discrete_Munit | apply (is_Discrete_distr0 (T.default k t)) ].
  Defined.


  Hypothesis foo: forall k (m1 m2:Mem.t k), 
   P m1 m2 ->  
   le_dist (d1i' m1) (d2i' m2) (lam k) (ep k).

  Let p k (m1 m2:Mem.t k) := 
   parity_split (D_points (d1'_discr m1)) (D_points (d2'_discr m2)).

  Hypothesis Hlam : forall k, (1 <= lam k)%R.

(*  



  Hypothesis HF : forall k (m1 m2:Mem.t k), 
   P m1 m2 -> serie (fun n => F k (p m1 m2 n)) <= ep k.

  Hypothesis Hdist : forall k (m1 m2:Mem.t k), 
   P m1 m2 -> 
   forall a,
    mu (d1i' m1) (carT k t a) - (lam k) ** (mu (d2i' m2) (carT k t a)) <= F k a /\
    mu (d2i' m2) (carT k t a) - (lam k) ** (mu (d1i' m1) (carT k t a)) <= F k a.
*)

  Lemma eequiv_random_assert :
   eequiv P 
   E1 [x1 <$- d1; Assert e1] 
   E2 [x2 <$- d2; Assert e2] 
   (EP_eq_expr x1 x2) lam ep.
  Proof.
   intros k m1 m2.
   set (d':=Mlet 
    (dmin (carT k t) (carT_cover k t) (p m1 m2) (d1i' m1)  (d2i' m2)) 
    (fun a => Munit (a, a))).
   assert (Hd':is_Discrete d') by 
    refine (is_Discrete_Mlet _ (is_discrete_Discrete _) (fun a => is_Discrete_Munit (a,a))).
   set (d'':=Mlet d' (fun vs => Munit (m1{!x1 <-- fst vs!}, m2{!x2 <-- snd vs!}))).
   exists d''; intros Hm.
   eapply le_lift_eq_compat with 
    (d1:= Mlet  (d1i' m1) (fun v => Munit (m1 {!x1 <-- v!})))
    (d2:= Mlet  (d2i' m2) (fun v => Munit (m2 {!x2 <-- v!}))) 
    (lam:= (lam k * R1)%R)
    (ep := (max (ep k + (lam k) ** 0) (0 + R1 ** ep k))); trivial.
   unfold d1i', drestr;
    rewrite (deno_cons _ (_ <$- _) [Assert _]), deno_random, 2 Mcomp;
    apply (Mlet_eq_compat (Oeq_refl _)); refine (ford_eq_intro _); intro v;
    rewrite Mlet_unit, deno_assert;
    case (E.eval_expr e1 (m1 {!x1 <-- v!})); 
     [ rewrite Mlet_unit; trivial | apply Mlet_distr0_abs ].
   unfold d2i', drestr;
    rewrite (deno_cons _ (_ <$- _) [Assert _]), deno_random, 2 Mcomp;
    apply (Mlet_eq_compat (Oeq_refl _)); refine (ford_eq_intro _); intro v;
    rewrite Mlet_unit, deno_assert;
    case (E.eval_expr e2 (m2 {!x2 <-- v!})); 
     [ rewrite Mlet_unit; trivial | apply Mlet_distr0_abs ].
   rewrite Rmult_1_r; auto.
   repeat multRU_simpl; repeat Usimpl; auto.
   refine (le_lift_Mlet _ _ _ _
    (cover_eq_prod _ _ (carT_cover _ _) (carT_cover _ _)) Hd' (Rle_refl _) _ _).
   eapply le_lift_weaken with (P:=@eq (T.interp k t)); 
    [ | | | apply (@le_lift_eq_intro _ _ 
     (carT_cover k t) _ _ 
     (d1'_discr m1) (d2'_discr m2) (lam k) 
     (ep k) (Hlam k)) ]; auto.
   intros v1 v2 Hv; subst; simpl.
   apply le_lift_Munit; trivial.
   unfold EP_eq_expr; simpl; rewrite 2 Mem.get_upd_same; trivial.
  Qed.
 
  Lemma eequiv_random_assert_strong: 
   (forall k (m1 m2:Mem.t k) v, 
    P m1 m2 -> 
    E.eval_expr e1 (m1{!x1 <-- v!}) = E.eval_expr e2 (m2{!x2 <-- v!})) ->
   eequiv P 
   E1 [x1 <$- d1; Assert e1] 
   E2 [x2 <$- d2; Assert e2] 
   (EP_eq_expr x1 x2 /-\ EP1 e1 /-\ EP2 e2) lam ep.
  Proof.
   intros Hequiv k m1 m2.
   set (d':=Mlet (dmin (carT k t) (carT_cover k t) (p m1 m2) (d1i' m1) (d2i' m2)) 
    (fun a => Munit (a, a))).
   assert (Hd':is_Discrete d') by 
    refine (is_Discrete_Mlet _ 
     (is_discrete_Discrete _) (fun a => is_Discrete_Munit (a,a))).
   set (d'':= Mlet d' 
    (fun vs => 
     if (E.eval_expr e1 (m1{!x1 <-- fst vs!}) && 
         E.eval_expr e2 (m2{!x2 <-- snd vs!})) then
     Munit (m1 {!x1 <-- fst vs!},m2 {!x2 <-- snd vs!}) else distr0 _)).
   exists d''; intros Hm.
   eapply le_lift_eq_compat with 
    (d1:=Mlet (d1i' m1) 
    (fun v => 
     if E.eval_expr e1 (m1{!x1 <-- v!}) then Munit (m1{!x1 <-- v!}) else distr0 _))
    (d2:= Mlet  (d2i' m2) 
    (fun v => 
     if E.eval_expr e2 (m2{!x2 <-- v!}) then Munit (m2{!x2 <-- v!}) else distr0 _))
    (lam:=(lam k * 1)%R)
    (ep :=max (ep k + (lam k) ** 0) (0 + 1%R ** ep k)); trivial.
   unfold d1i', drestr;
   rewrite (deno_cons _ (_ <$- _) [Assert _]), deno_random, 2 Mcomp;
   apply (Mlet_eq_compat (Oeq_refl _)); refine (ford_eq_intro _); 
   intro v; rewrite Mlet_unit; rewrite deno_assert.
   case_eq (E.eval_expr e1 (m1 {!x1 <-- v!})); intro Heq;
    [rewrite Mlet_unit, Heq | apply Mlet_distr0_abs; rewrite Heq]; trivial.
   unfold d2i', drestr;
   rewrite (deno_cons _ (_ <$- _) [Assert _]), deno_random, 2 Mcomp;
    apply (Mlet_eq_compat (Oeq_refl _)); refine (ford_eq_intro _); intro v;
    rewrite Mlet_unit, deno_assert;
    case_eq (E.eval_expr e2 (m2 {!x2 <-- v!})); intro Heq;
     [ rewrite Mlet_unit; rewrite Heq; trivial | apply Mlet_distr0_abs ].
   rewrite Rmult_1_r; auto.
   repeat multRU_simpl; repeat Usimpl; auto.

   refine (le_lift_Mlet _ _ _ _
    (cover_eq_prod _ _ (carT_cover _ _) (carT_cover _ _)) Hd' (Rle_refl _) _ _).
   eapply le_lift_weaken with (P:=@eq (T.interp k t)); 
    [ | | | apply (@le_lift_eq_intro _ _ (carT_cover k t) _ _
     (d1'_discr m1) (d2'_discr m2) (lam k) (ep k) (Hlam k)) ]; auto.
   intros v1 v2 Hv; subst; simpl.
   case_eq (E.eval_expr e1 (m1 {!x1 <-- v2!})); intros H1;
    case_eq (E.eval_expr e2 (m2 {!x2 <-- v2!})); intros H2; simpl.
   apply le_lift_Munit; trivial.
   unfold EP_eq_expr; simpl; repeat split. 
   rewrite 2 Mem.get_upd_same; trivial.
   unfold EP1; trivial.
   unfold EP2; trivial.
   rewrite Hequiv with (m2:=m2) in H1.
   rewrite H2 in H1; discriminate H1.
   rewrite Hequiv with (m2:=m2) in H1.
   rewrite H2 in H1; discriminate H1.
   trivial.
   rewrite Hequiv with (m2:=m2) in H1.
   rewrite H2 in H1; discriminate H1.
   rewrite Hequiv with (m2:=m2) in H1.
   rewrite H2 in H1; discriminate H1.
   trivial.
   apply le_lift_distr0.
   trivial.
  Qed.

 End RANDOM_ASSERT.


 Lemma deno_app_assert_elim : forall k e E c (m:Mem.t k) f, 
  mu ([[c]] E m) f ==
  mu ([[ c ++ [Assert e] ]] E m) f + mu ([[ c ++ [Assert !e] ]] E m) f.
 Proof.
  intros.
  rewrite deno_app_elim, deno_app_elim.
  eapply Oeq_trans; [ | apply mu_stable_plus].
  apply mu_stable_eq.
  refine (ford_eq_intro _); intro m'; unfold fplus.
  repeat rewrite deno_assert_elim; rewrite eval_negb.
  case (E.eval_expr e m'); simpl; auto.
  intros m'; unfold finv.
  repeat rewrite deno_assert_elim; rewrite eval_negb.
  case (E.eval_expr e m'); simpl; auto.
 Qed.


 Section MPLUS.
  
  Variable A : Type.
  
  Variable P : A -o> boolO.
  
  Variables d1 d2 : Distr A.
  
  Hypothesis range_1 : range P d1.
  
  Hypothesis range_2 : range (negP P) d2.

  Hypothesis le_inv : mu d1 (fone _) <= [1-] mu d2 (fone _).

  Lemma le_inv_generalize : forall f, mu d1 f <= [1-] mu d2 f.
  Proof.
   intros.
   transitivity (mu d1 (fone _)).
   auto.
   transitivity ([1-] mu d2 (fone _));  auto.
  Qed.
 
  Definition mu_plus : (A -O-> U) -M-> U.
   exists (fun f => mu d1 f + mu d2 f).
   intros f g Hfg.
   apply Uplus_le_compat; apply mu_monotonic; trivial.
  Defined.
 
  Definition Mplus : Distr A.
   refine (@Build_distr A mu_plus _ _ _ _).
   intros f; simpl.
   apply Uplus_notoverflow.
   transitivity (iR (mu d1 (fone _)) + iR (mu d2 (fone _)))%R.
   rewrite (mu_inv_minus d1 f), (mu_inv_minus d2 f), 2 iR_minus.
   simpl. 
   fourier.
   apply iR_le; apply mu_monotonic; auto.
   apply iR_le; apply mu_monotonic; auto.
   assert (iR ((mu d1) (fone A)) <= 1 - iR ((mu d2) (fone A)))%R
    by (rewrite <- iR_inv; apply iR_le; auto); fourier.
   
   intros f g Hfg.
   unfold fplus; simpl.
   rewrite (mu_stable_plus d1 Hfg).
   rewrite (mu_stable_plus d2 Hfg).
   repeat rewrite <-Uplus_assoc.
   apply Uplus_eq_compat; trivial.
   
   intros a f.
   unfold fmult; simpl.
   rewrite (mu_stable_mult d1 a f).
   rewrite (mu_stable_mult d2 a f).
   rewrite Udistr_plus_left.
   trivial.
   apply le_inv_generalize.

   intros F.
   simpl.
   rewrite (mu_continuous d1 F).
   rewrite (mu_continuous d2 F).   
   rewrite <-lub_eq_plus.
   apply lub_le_compat.
   simpl; trivial.
  Defined.

  Lemma Mplus_elim : forall f,
   mu Mplus f == mu d1 f + mu d2 f.
  Proof.
   intros; unfold Mplus; trivial.
  Qed.

 End MPLUS.   


 Lemma eequiv_assert_app : forall E1 E2 c1 c1' c2 c2' e1 e2 P Q lam1 lam2,
  (forall k, 1 <= lam1 k)%R ->
  (forall k, 1 <= lam2 k)%R ->
  decMR P ->
  eequiv P 
  E1 (c1 ++ [Assert e1] ++ c1') 
  E2 (c2 ++ [Assert e2] ++ c2')
  Q lam1 (fun k => 0) -> 
  eequiv P 
  E1 (c1 ++ [Assert !e1] ++ c1') 
  E2 (c2 ++ [Assert !e2] ++ c2')
  Q lam2 (fun k => 0) -> 
  eequiv P 
  E1 (c1 ++ c1')
  E2 (c2 ++ c2')
  Q 
  (fun k => Rmax (lam1 k) (lam2 k)) (fun k => 0).
 Proof.
  unfold eequiv; intros E1 E2 c1 c1' c2 c2' e1 e2 P Q lam1 lam2 Hlam1 Hlam2 HP
   H1 H2 k m1 m2.
  destruct (H1 k m1 m2) as [d1 Hd1]; clear H1.
  destruct (H2 k m1 m2) as [d2 Hd2]; clear H2.
  case (HP k m1 m2); clear HP; intro HP; [ | exists (distr0 _); tauto].
  
  assert (W:mu d1 (fone _) <= [1-] mu d2 (fone _)).
  destruct (Hd1 HP); clear Hd1.
  destruct (Hd2 HP); clear Hd2.

  transitivity (mu (Mfst d1) (fone _)).
  simpl; refine (mu_monotonic _ _ _ _); trivial.
  transitivity ([1-] mu (Mfst d2) (fone _));
   [ | simpl; apply Uinv_le_compat; refine (mu_monotonic _ _ _ _); trivial].
  rewrite le_p1.
  rewrite deno_app_elim.
  eapply Ole_trans; [ | apply Uinv_le_compat; apply le_p0].
  rewrite deno_app_elim.
  eapply Ole_trans; [ | apply mu_stable_inv ].
  refine (mu_monotonic _ _ _ _); intro.
  unfold finv.
  rewrite deno_app_elim, deno_app_elim.
  rewrite deno_assert_elim, deno_assert_elim, eval_negb.
  case (E.eval_expr e1 x); unfold finv, fone; simpl; auto.
  
  exists (Mplus d1 d2 W); intro.
  constructor; trivial.
  apply Rmax_case; trivial.

  intros; apply max_le.
  apply d_expr_le_intro.
  apply Rmax_case; trivial.

  simpl.
  destruct (Hd1 HP); clear Hd1.
  destruct (Hd2 HP); clear Hd2.
  rewrite <-multRU_distr_plus_l; [ | trivial].
  generalize (le_d  f g); clear le_d;  intros.
  generalize (le_d0 f g); clear le_d0; intros.
  
  rewrite (deno_app_elim E1 c1 c1' m1).
  rewrite mu_restr_split with (P:=EP k e1) (d:=[[c1]] E1 m1).
  eapply Ole_trans.
  apply Uplus_minus_perm_assoc.
  assert 
   (d_expr (Mfst d1) ([[ c1 ++ [Assert e1] ++ c1' ]] E1 m1) (lam1 k) f f <= 0).
  rewrite <-H0; apply max_le_right; clear H0.
  assert 
   (d_expr (Mfst d2) ([[ c1 ++ [Assert !e1] ++ c1' ]] E1 m1) (lam2 k) f f <= 0).
  rewrite <-H1; apply max_le_right; clear H1.
  apply d_expr_le_elim in H2; destruct H2.
  apply d_expr_le_elim in H3; destruct H3.
  unfold restr; clear H4 H5.
  rewrite <-(Uplus_zero_left 0); apply Uplus_le_compat.
  rewrite deno_app_elim in H2.
  simpl in H2. 
  rewrite <-H2.
  apply Uminus_le_compat.
  apply mu_monotonic; intro m'.
  rewrite (deno_cons_elim E1 (Assert e1) c1' m'), Mlet_simpl.
  rewrite deno_assert_elim; trivial.
  apply multRU_le_compat.
  fourier.
  apply Rmax_l.
  trivial.
  
  rewrite deno_app_elim in H3.
  simpl in H3. 
  rewrite <-H3.
  apply Uminus_le_compat.
  apply mu_monotonic; intro m'.
  rewrite (deno_cons_elim E1 (Assert !e1) c1' m'), Mlet_simpl.
  rewrite deno_assert_elim; trivial.
  apply multRU_le_compat.
  fourier.
  apply Rmax_r.
  trivial.

  apply Rmax_case; trivial.

  simpl.
  destruct (Hd1 HP); clear Hd1.
  destruct (Hd2 HP); clear Hd2.
  generalize (le_p0 f); clear le_p0; intros.
  generalize (le_p1 f); clear le_p1; intros.

  rewrite (deno_app_elim E1 c1 c1' m1).
  rewrite mu_restr_split with (P:=EP k e1) (d:=[[c1]] E1 m1).
  unfold restr.
  rewrite <-multRU_distr_plus_l.
  eapply Ole_trans.
  apply Uplus_minus_perm_assoc.
  rewrite <-(Uplus_zero_left 0); apply Uplus_le_compat.

  rewrite deno_app_elim in H1.
  simpl in H1. 
  apply Uminus_le_zero.
  rewrite H1.
  eapply Ole_trans.
  apply multRU_ge1 with (x:=Rmax (lam1 k) (lam2 k)).
  apply Rmax_case; trivial.
  apply multRU_le_compat.
  apply Rmax_case; fourier.
  trivial.
  refine (mu_monotonic _ _ _ _); intro m'.
  rewrite (deno_cons_elim E1 (Assert e1) c1' m'), Mlet_simpl.
  rewrite deno_assert_elim; trivial.

  rewrite deno_app_elim in H0.
  simpl in H0. 
  apply Uminus_le_zero.
  rewrite H0.
  eapply Ole_trans.
  apply multRU_ge1 with (x:=Rmax (lam1 k) (lam2 k)).
  apply Rmax_case; trivial.
  apply multRU_le_compat.
  apply Rmax_case; fourier.
  trivial.
  refine (mu_monotonic _ _ _ _); intro m'.
  rewrite (deno_cons_elim E1 (Assert !e1) c1' m'), Mlet_simpl.
  rewrite deno_assert_elim; trivial.
  
  apply Rmax_case; trivial.

  (* Idem *)
  apply d_expr_le_intro.
  apply Rmax_case; trivial.

  simpl.
  destruct (Hd1 HP); clear Hd1.
  destruct (Hd2 HP); clear Hd2.
  rewrite <-multRU_distr_plus_l; [ | trivial].
  generalize (le_d  f g); clear le_d;  intros.
  generalize (le_d0 f g); clear le_d0; intros.
  
  rewrite (deno_app_elim E2 c2 c2' m2).
  rewrite mu_restr_split with (P:=EP k e2) (d:=[[c2]] E2 m2).
  eapply Ole_trans.
  apply Uplus_minus_perm_assoc.
  assert 
   (d_expr (Msnd d1) ([[ c2 ++ [Assert e2] ++ c2' ]] E2 m2) (lam1 k) g g <= 0).
  rewrite <-H0; apply max_le_left; clear H0.
  assert 
   (d_expr (Msnd d2) ([[ c2 ++ [Assert !e2] ++ c2' ]] E2 m2) (lam2 k) g g <= 0).
  rewrite <-H1; apply max_le_left; clear H1.
  apply d_expr_le_elim in H2; destruct H2.
  apply d_expr_le_elim in H3; destruct H3.
  unfold restr; clear H4 H5.
  rewrite <-(Uplus_zero_left 0); apply Uplus_le_compat.
  rewrite deno_app_elim in H2.
  simpl in H2. 
  rewrite <-H2.
  apply Uminus_le_compat.
  apply mu_monotonic; intro m'.
  rewrite (deno_cons_elim E2 (Assert e2) c2' m'), Mlet_simpl.
  rewrite deno_assert_elim; trivial.
  unfold EP.
  apply multRU_le_compat.
  fourier.
  apply Rmax_l.
  trivial.
  
  rewrite deno_app_elim in H3.
  simpl in H3. 
  rewrite <-H3.
  apply Uminus_le_compat.
  apply mu_monotonic; intro m'.
  rewrite (deno_cons_elim E2 (Assert !e2) c2' m'), Mlet_simpl.
  rewrite deno_assert_elim; trivial.
  apply multRU_le_compat.
  fourier.
  apply Rmax_r.
  trivial.

  apply Rmax_case; trivial.

  simpl.
  destruct (Hd1 HP); clear Hd1.
  destruct (Hd2 HP); clear Hd2.
  generalize (le_p2 g); clear le_p2; intros.
  generalize (le_p3 g); clear le_p3; intros.

  rewrite (deno_app_elim E2 c2 c2' m2).
  rewrite mu_restr_split with (P:=EP k e2) (d:=[[c2]] E2 m2).
  unfold restr.
  rewrite <-multRU_distr_plus_l.
  eapply Ole_trans.
  apply Uplus_minus_perm_assoc.
  rewrite <-(Uplus_zero_left 0); apply Uplus_le_compat.

  rewrite deno_app_elim in H0.
  simpl in H0. 
  apply Uminus_le_zero.
  rewrite H0.
  eapply Ole_trans.
  apply multRU_ge1 with (x:=Rmax (lam1 k) (lam2 k)).
  apply Rmax_case; trivial.
  apply multRU_le_compat.
  apply Rmax_case; fourier.
  trivial.
  refine (mu_monotonic _ _ _ _); intro m'.
  rewrite (deno_cons_elim E2 (Assert e2) c2' m'), Mlet_simpl.
  rewrite deno_assert_elim; trivial.

  rewrite deno_app_elim in H1.
  simpl in H1. 
  apply Uminus_le_zero.
  rewrite H1.
  eapply Ole_trans.
  apply multRU_ge1 with (x:=Rmax (lam1 k) (lam2 k)).
  apply Rmax_case; trivial.
  apply multRU_le_compat.
  apply Rmax_case; fourier.
  trivial.
  refine (mu_monotonic _ _ _ _); intro m'.
  rewrite (deno_cons_elim E2 (Assert !e2) c2' m'), Mlet_simpl.
  rewrite deno_assert_elim; trivial.
  
  apply Rmax_case; trivial.

  (* Finally *)
  intros ? ?.
  rewrite Mplus_elim.
  rewrite <-Uplus_zero_left; apply Uplus_eq_compat.
  destruct (Hd1 HP); apply le_r; trivial.
  destruct (Hd2 HP); apply le_r; trivial.

  intros.
  rewrite deno_app_elim.
  rewrite mu_restr_split with (P:=EP k e1) (d:=[[c1]] E1 m1).
  unfold restr, Mfst; rewrite Mlet_simpl, Mplus_elim.
  apply Uplus_le_compat.
  destruct (Hd1 HP).
  unfold Mfst in le_p1.
  simpl in le_p1 |- *.
  rewrite le_p1.
  rewrite (deno_app_elim E1 c1 ((Assert e1) :: c1') m1).
  apply mu_monotonic; intro m'.
  rewrite deno_cons_elim, Mlet_simpl, deno_assert_elim; trivial.
  
  destruct (Hd2 HP).
  unfold Mfst in le_p1.
  simpl in le_p1 |- *.
  rewrite le_p1.
  rewrite (deno_app_elim E1 c1 ((Assert !e1) :: c1') m1).
  apply mu_monotonic; intro m'.
  rewrite deno_cons_elim, Mlet_simpl, deno_assert_elim; trivial.

  intros.
  rewrite deno_app_elim.
  rewrite mu_restr_split with (P:=EP k e2) (d:=[[c2]] E2 m2).
  unfold restr, Msnd; rewrite Mlet_simpl, Mplus_elim.
  apply Uplus_le_compat.
  destruct (Hd1 HP).
  unfold Msnd in le_p2.
  simpl in le_p2 |- *.
  rewrite le_p2.
  rewrite (deno_app_elim E2 c2 ((Assert e2) :: c2') m2).
  apply mu_monotonic; intro m'.
  rewrite deno_cons_elim, Mlet_simpl, deno_assert_elim; trivial.
  
  destruct (Hd2 HP).
  unfold Msnd in le_p2.
  simpl in le_p2 |- *.
  rewrite le_p2.
  rewrite (deno_app_elim E2 c2 ((Assert !e2) :: c2') m2).
  apply mu_monotonic; intro m'.
  rewrite deno_cons_elim, Mlet_simpl, deno_assert_elim; trivial.
 Qed.
 
 Lemma eequiv_assert_join : forall E1 E2 e1 e2 c1 c2 P Q lam1 lam2,
  (forall k, 1 <= lam1 k)%R ->
  (forall k, 1 <= lam2 k)%R ->
  eequiv P E1 (c1 ++ [Assert  e1]) E2 (c2 ++ [Assert  e2]) Q lam1 (fun k => 0) ->
  eequiv P E1 (c1 ++ [Assert !e1]) E2 (c2 ++ [Assert !e2]) Q lam2 (fun k => 0) ->
  decMR P ->
  eequiv P E1 c1 E2 c2 Q (fun k => Rmax (lam1 k) (lam2 k)) (fun k => 0).
 Proof.
  unfold eequiv.
  intros E1 E2 e1 e2 c1 c2 P Q lam1 lam2 Hlam1 Hlam2 H1 H2 HP k m1 m2.
  destruct (H1 k m1 m2) as [d1 Hd1]; clear H1. 
  destruct (H2 k m1 m2) as [d2 Hd2]; clear H2.
  destruct (HP _ m1 m2) as [Hm | Hm].

  assert (W:mu d1 (fone _) <= [1-] mu d2 (fone _)).
  destruct (Hd1 Hm); clear Hd1.
  destruct (Hd2 Hm); clear Hd2.

  transitivity (mu (Mfst d1) (fone _)).
  simpl; refine (mu_monotonic _ _ _ _); trivial.
  transitivity ([1-] mu (Mfst d2) (fone _));
   [ | simpl; apply Uinv_le_compat; refine (mu_monotonic _ _ _ _); trivial].
  rewrite le_p1.
  rewrite deno_app_elim.
  eapply Ole_trans; [ | apply Uinv_le_compat; apply le_p0].
  rewrite deno_app_elim.
  eapply Ole_trans; [ | apply mu_stable_inv ].
  refine (mu_monotonic _ _ _ _); intro.
  unfold finv.
  rewrite deno_assert_elim, deno_assert_elim, eval_negb.
  case (E.eval_expr e1 x); unfold finv, fone; simpl; auto.
   
  exists (Mplus d1 d2 W).
  apply (Rmax_case_strong (lam1 k) (lam2 k)); intros Hle H.

  (* lam2 <= lam1 *)
  destruct (Hd1 H); clear Hd1.
  destruct (Hd2 H); clear Hd2.  
  constructor; intros; trivial.
  apply max_le; apply d_expr_le_intro; simpl; trivial.

  rewrite <-multRU_distr_plus_l; [ | trivial].
  generalize (le_d  f g); clear le_d;  intros.
  generalize (le_d0 f g); clear le_d0; intros.
  assert (d_expr (Mfst d1) ([[ c1 ++ [Assert e1] ]] E1 m1) (lam1 k) f f <= 0).
  rewrite <-H0; apply max_le_right; clear H0.
  assert (d_expr (Mfst d2) ([[ c1 ++ [Assert !e1] ]] E1 m1) (lam2 k) f f <= 0).
  rewrite <-H1; apply max_le_right; clear H1.
  apply d_expr_le_elim in H2; destruct H2.
  apply d_expr_le_elim in H3; destruct H3.
  clear H0 H1 H4 H5.

  generalize (Uminus_zero_le (Ule_zero_eq _ H2)); clear H2; intro H1.   
  generalize (Uminus_zero_le (Ule_zero_eq _ H3)); clear H3; intro H2.
  apply Uminus_le_zero.
  rewrite (deno_app_assert_elim e1 E1 c1 m1).
  rewrite H1, H2. 
  apply Uplus_le_compat; trivial.
  apply multRU_le_compat; trivial.
  fourier. 

  simpl in le_p0, le_p1; rewrite le_p0, le_p1.
  generalize (le_d  f g); clear le_d;  intros.
  generalize (le_d0 f g); clear le_d0; intros.
  assert (d_expr (Mfst d1) ([[ c1 ++ [Assert e1] ]] E1 m1) (lam1 k) f f <= 0).
  rewrite <-H0; apply max_le_right; clear H0.
  assert (d_expr (Mfst d2) ([[ c1 ++ [Assert !e1] ]] E1 m1) (lam2 k) f f <= 0).
  rewrite <-H1; apply max_le_right; clear H1.
  apply d_expr_le_elim in H2; destruct H2.
  apply d_expr_le_elim in H3; destruct H3.
  clear H0 H1 H4 H5.
  rewrite (deno_app_assert_elim e1 E1 c1 m1).
  rewrite <-multRU_distr_plus_l; trivial.
  apply Uminus_le_zero.
  apply Uplus_le_compat; apply multRU_ge1; trivial.

  rewrite <-multRU_distr_plus_l; [ | trivial].
  generalize (le_d  f g); clear le_d;  intros.
  generalize (le_d0 f g); clear le_d0; intros.
  assert (d_expr (Msnd d1) ([[ c2 ++ [Assert e2] ]] E2 m2) (lam1 k) g g <= 0).
  rewrite <-H0; apply max_le_left; clear H0.
  assert (d_expr (Msnd d2) ([[ c2 ++ [Assert !e2] ]] E2 m2) (lam2 k) g g <= 0).
  rewrite <-H1; apply max_le_left; clear H1.
  apply d_expr_le_elim in H2; destruct H2.
  apply d_expr_le_elim in H3; destruct H3.
  clear H0 H1 H4 H5.

  generalize (Uminus_zero_le (Ule_zero_eq _ H2)); clear H2; intro H1.   
  generalize (Uminus_zero_le (Ule_zero_eq _ H3)); clear H3; intro H2.
  apply Uminus_le_zero.
  rewrite (deno_app_assert_elim e2 E2 c2 m2).
  rewrite H1, H2. 
  apply Uplus_le_compat; trivial.
  apply multRU_le_compat; trivial.
  fourier. 

  simpl in le_p2, le_p3; rewrite le_p2, le_p3.
  generalize (le_d  f g); clear le_d;  intros.
  generalize (le_d0 f g); clear le_d0; intros.
  assert (d_expr (Msnd d1) ([[ c2 ++ [Assert e2] ]] E2 m2) (lam1 k) g g <= 0).
  rewrite <-H0; apply max_le_left; clear H0.
  assert (d_expr (Msnd d2) ([[ c2 ++ [Assert !e2] ]] E2 m2) (lam2 k) g g <= 0).
  rewrite <-H1; apply max_le_left; clear H1.
  apply d_expr_le_elim in H2; destruct H2.
  apply d_expr_le_elim in H3; destruct H3.
  clear H0 H1 H4 H5.
  rewrite (deno_app_assert_elim e2 E2 c2 m2).
  rewrite <-multRU_distr_plus_l; trivial.
  apply Uminus_le_zero.
  apply Uplus_le_compat; apply multRU_ge1; trivial.

  intros f Hf; simpl.
  rewrite <-Uplus_zero_left; apply Uplus_eq_compat; auto.

  rewrite (deno_app_assert_elim e1 E1 c1 m1).
  simpl in le_p0, le_p1 |- *; rewrite le_p0, le_p1; trivial.

  rewrite (deno_app_assert_elim e2 E2 c2 m2); trivial.
  simpl in le_p2, le_p3 |- *; rewrite le_p2, le_p3; trivial.
 
  (* lam1 <= lam2 *)
  destruct (Hd1 H); clear Hd1.
  destruct (Hd2 H); clear Hd2.  
  constructor; intros; trivial.
  apply max_le; apply d_expr_le_intro; simpl; trivial.

  rewrite <-multRU_distr_plus_l; [ | trivial].
  generalize (le_d  f g); clear le_d;  intros.
  generalize (le_d0 f g); clear le_d0; intros.
  assert (d_expr (Mfst d1) ([[ c1 ++ [Assert e1] ]] E1 m1) (lam1 k) f f <= 0).
  rewrite <-H0; apply max_le_right; clear H0.
  assert (d_expr (Mfst d2) ([[ c1 ++ [Assert !e1] ]] E1 m1) (lam2 k) f f <= 0).
  rewrite <-H1; apply max_le_right; clear H1.
  apply d_expr_le_elim in H2; destruct H2.
  apply d_expr_le_elim in H3; destruct H3.
  clear H0 H1 H4 H5.

  generalize (Uminus_zero_le (Ule_zero_eq _ H2)); clear H2; intro H1.   
  generalize (Uminus_zero_le (Ule_zero_eq _ H3)); clear H3; intro H2.
  apply Uminus_le_zero.
  rewrite (deno_app_assert_elim e1 E1 c1 m1).
  rewrite H1, H2. 
  apply Uplus_le_compat; trivial.
  apply multRU_le_compat; trivial.
  fourier. 

  simpl in le_p0, le_p1; rewrite le_p0, le_p1.
  generalize (le_d  f g); clear le_d;  intros.
  generalize (le_d0 f g); clear le_d0; intros.
  assert (d_expr (Mfst d1) ([[ c1 ++ [Assert e1] ]] E1 m1) (lam1 k) f f <= 0).
  rewrite <-H0; apply max_le_right; clear H0.
  assert (d_expr (Mfst d2) ([[ c1 ++ [Assert !e1] ]] E1 m1) (lam2 k) f f <= 0).
  rewrite <-H1; apply max_le_right; clear H1.
  apply d_expr_le_elim in H2; destruct H2.
  apply d_expr_le_elim in H3; destruct H3.
  clear H0 H1 H4 H5.
  rewrite (deno_app_assert_elim e1 E1 c1 m1).
  rewrite <-multRU_distr_plus_l; trivial.
  apply Uminus_le_zero.
  apply Uplus_le_compat; apply multRU_ge1; trivial.

  rewrite <-multRU_distr_plus_l; [ | trivial].
  generalize (le_d  f g); clear le_d;  intros.
  generalize (le_d0 f g); clear le_d0; intros.
  assert (d_expr (Msnd d1) ([[ c2 ++ [Assert e2] ]] E2 m2) (lam1 k) g g <= 0).
  rewrite <-H0; apply max_le_left; clear H0.
  assert (d_expr (Msnd d2) ([[ c2 ++ [Assert !e2] ]] E2 m2) (lam2 k) g g <= 0).
  rewrite <-H1; apply max_le_left; clear H1.
  apply d_expr_le_elim in H2; destruct H2.
  apply d_expr_le_elim in H3; destruct H3.
  clear H0 H1 H4 H5.

  generalize (Uminus_zero_le (Ule_zero_eq _ H2)); clear H2; intro H1.   
  generalize (Uminus_zero_le (Ule_zero_eq _ H3)); clear H3; intro H2.
  apply Uminus_le_zero.
  rewrite (deno_app_assert_elim e2 E2 c2 m2).
  rewrite H1, H2. 
  apply Uplus_le_compat; trivial.
  apply multRU_le_compat; trivial.
  fourier. 

  simpl in le_p2, le_p3; rewrite le_p2, le_p3.
  generalize (le_d  f g); clear le_d;  intros.
  generalize (le_d0 f g); clear le_d0; intros.
  assert (d_expr (Msnd d1) ([[ c2 ++ [Assert e2] ]] E2 m2) (lam1 k) g g <= 0).
  rewrite <-H0; apply max_le_left; clear H0.
  assert (d_expr (Msnd d2) ([[ c2 ++ [Assert !e2] ]] E2 m2) (lam2 k) g g <= 0).
  rewrite <-H1; apply max_le_left; clear H1.
  apply d_expr_le_elim in H2; destruct H2.
  apply d_expr_le_elim in H3; destruct H3.
  clear H0 H1 H4 H5.
  rewrite (deno_app_assert_elim e2 E2 c2 m2).
  rewrite <-multRU_distr_plus_l; trivial.
  apply Uminus_le_zero.
  apply Uplus_le_compat; apply multRU_ge1; trivial.

  intros f Hf; simpl.
  rewrite <-Uplus_zero_left; apply Uplus_eq_compat; auto.

  rewrite (deno_app_assert_elim e1 E1 c1 m1).
  simpl in le_p0, le_p1 |- *; rewrite le_p0, le_p1; trivial.

  rewrite (deno_app_assert_elim e2 E2 c2 m2); trivial.
  simpl in le_p2, le_p3 |- *; rewrite le_p2, le_p3; trivial.

  exists d1.
  intro; contradiction.
 Qed.

 (** TODO: This should be in SemTheory.v, but depends on too much things *)
 Lemma equiv_assert_app : forall E1 E2 c1 c1' c2 c2' e1 e2 P Q,
  decMR P ->
  equiv P 
  E1 (c1 ++ [Assert e1] ++ c1') 
  E2 (c2 ++ [Assert e2] ++ c2')
  Q -> 
  equiv P 
  E1 (c1 ++ [Assert !e1] ++ c1') 
  E2 (c2 ++ [Assert !e2] ++ c2')
  Q -> 
  equiv P 
  E1 (c1 ++ c1')
  E2 (c2 ++ c2')
  Q.
 Proof.
  intros E1 E2 c1 c1' c2 c2' e1 e2 P Q HP H1 H2.
  apply eequiv_equiv.
  eapply eequiv_weaken with (lam':=fun _ => _); [ | | | |  
   eapply eequiv_assert_app with e1 e2]; auto using equiv_eequiv; trivial.
  intro; apply Rmax_lub; trivial.
 Qed.

 Lemma equiv_eq_compat_l : forall (P Q:mem_rel) E1 E2 c1 c1' c2,
  (forall k (m1 m2:Mem.t k) f, 
   P k m1 m2 -> mu ([[c1]] E1 m1) f == mu ([[c1']] E1 m1) f) ->
  equiv P E1 c1  E2 c2 Q ->
  equiv P E1 c1' E2 c2 Q.
 Proof.
  intros P Q E1 E2 c1 c1' c2 Heq Hequiv k.
  destruct (choice (fun (mm:Mem.t k * Mem.t k) (dd:Distr(Mem.t k * Mem.t k)) =>  
   P k (fst mm) (snd mm) ->
   lift (Q k) dd (([[ c1 ]]) E1 (fst mm)) (([[ c2 ]]) E2 (snd mm)))) as (d',Hd').
  intros (m1,m2).
  destruct (Hequiv k) as [d Hd]; exists (d m1 m2); auto.
  exists (fun m1 m2 => d' (m1,m2)); intros; auto.
  assert (X:=fun f => Heq k m1 m2 f H).
  apply eq_distr_intro in X.
  rewrite <-X; apply Hd'; trivial.
 Qed. 

 Lemma equiv_eq_compat_r : forall (P Q:mem_rel) E1 E2 c1 c2 c2',
  (forall k (m1 m2:Mem.t k) f, 
   P k m1 m2 -> mu ([[c2]] E2 m2) f == mu ([[c2']] E2 m2) f) ->
  equiv P E1 c1 E2 c2  Q ->
  equiv P E1 c1 E2 c2' Q.
 Proof.
  intros P Q E1 E2 c1 c2 c2' Heq Hequiv k.
  destruct (choice (fun (mm:Mem.t k * Mem.t k) (dd:Distr(Mem.t k * Mem.t k)) =>  
   P k (fst mm) (snd mm) ->
   lift (Q k) dd (([[ c1 ]]) E1 (fst mm)) (([[ c2 ]]) E2 (snd mm)))) as (d',Hd').
  intros (m1,m2).
  destruct (Hequiv k) as [d Hd]; exists (d m1 m2); auto.
  exists (fun m1 m2 => d' (m1,m2)); intros; auto.
  assert (X:=fun f => Heq k m1 m2 f H).
  apply eq_distr_intro in X.
  rewrite <-X; apply Hd'; trivial.
 Qed.

(* 
** If-neg rule                                                               
**                                                                            
**   c1; if ~e then c3 else c2; c4 ~  d : P ==> Q                         
**  -----------------------------------------------   
**   c1; if e then c2 else c3; c4 ~  d : P ==> Q                       
*)

 Lemma equiv_cond_neg_l : forall E1 E2 c1 c2 c3 c4 d e P Q,
  equiv P E1 (c1 ++ [If !e then c3 else c2] ++ c4) E2 d Q ->
  equiv P E1 (c1 ++ [If e then c2 else c3] ++ c4) E2 d Q.
 Proof.
  intros.
  apply equiv_eq_compat_l with (2:=H); intros.
  rewrite deno_app_elim, deno_app_elim.
  apply mu_stable_eq; intros; refine (ford_eq_intro _); intro m.
  rewrite deno_app_elim, deno_app_elim, deno_cond_elim, deno_cond_elim.
  rewrite eval_negb; case (E.eval_expr e m); trivial.
 Qed.

 Lemma equiv_cond_neg_r : forall E1 E2 c d1 d2 d3 d4 e P Q,
  equiv P E1 c E2 (d1 ++ [If !e then d3 else d2] ++ d4) Q ->
  equiv P E1 c E2 (d1 ++ [If e then d2 else d3] ++ d4) Q.
 Proof.
  intros.
  apply equiv_eq_compat_r with (2:=H); intros.
  rewrite deno_app_elim, deno_app_elim.
  apply mu_stable_eq; intros; refine (ford_eq_intro _); intro m.
  rewrite deno_app_elim, deno_app_elim, deno_cond_elim, deno_cond_elim.
  rewrite eval_negb; case (E.eval_expr e m); trivial.
 Qed.

 (* 
 ** If-sync rule                                                             
 **                                                                            
 **        c1; assert  e; c2; c4 ~ d1; assert  f; d2; d4 : P ==> Q             
 **        c1; assert !e; c3; c4 ~ d1; assert !f; d3; d4 : P ==> Q             
 **        c1 ~ d1 : P ==> e<1> = f<2>                                         
 **  --------------------------------------------------------------------           
 **  c1; if e then c2 else c3; c4 ~ d1; if f then d2 else d3; d4: P ==> Q      
 **                                                                            
 *)

 Lemma equiv_cond_sync : forall E1 E2 c1 c2 c3 c4 d1 d2 d3 d4 e f P Q,
  decMR P ->
  equiv P 
  E1 (c1 ++ [Assert e] ++ c2 ++ c4) 
  E2 (d1 ++ [Assert f] ++ d2 ++ d4) Q ->
  equiv P 
  E1 (c1 ++ [Assert !e] ++ c3 ++ c4) 
  E2 (d1 ++ [Assert !f] ++ d3 ++ d4) Q ->
  equiv P E1 c1 E2 d1 (fun k m1 m2 => E.eval_expr e m1 = E.eval_expr f m2) ->
  equiv P 
  E1 (c1 ++ [If e then c2 else c3] ++ c4) 
  E2 (d1 ++ [If f then d2 else d3] ++ d4) Q.
 Proof.
  intros.
  apply equiv_assert_app with e f; trivial.
  apply equiv_eq_compat_l with (c1 ++ [Assert e] ++ c2 ++ c4); intros.

  rewrite deno_app_elim, deno_app_elim; apply mu_stable_eq.
  refine (ford_eq_intro _); intro m.
  rewrite deno_app_elim, deno_assert_elim.
  symmetry; rewrite deno_app_elim, deno_assert_elim.  
  case_eq (E.eval_expr e m); intro; [ | trivial].
  rewrite deno_app_elim, deno_app_elim, deno_cond_t_elim; trivial.

  apply equiv_eq_compat_r with (d1 ++ [Assert f] ++ d2 ++ d4); intros.

  rewrite deno_app_elim, deno_app_elim; apply mu_stable_eq.
  refine (ford_eq_intro _); intro m.
  rewrite deno_app_elim, deno_assert_elim.
  symmetry; rewrite deno_app_elim, deno_assert_elim.  
  case_eq (E.eval_expr f m); intro; [ | trivial].
  rewrite deno_app_elim, deno_app_elim, deno_cond_t_elim; trivial.

  trivial.

  apply equiv_eq_compat_l with (c1 ++ [Assert !e] ++ c3 ++ c4); intros.

  rewrite deno_app_elim, deno_app_elim; apply mu_stable_eq.
  refine (ford_eq_intro _); intro m.
  rewrite deno_app_elim, deno_assert_elim.
  symmetry; rewrite deno_app_elim, deno_assert_elim.
  rewrite eval_negb; case_eq (E.eval_expr e m); intro; [trivial | ].
  simpl negb; cbv iota.
  rewrite deno_app_elim, deno_app_elim, (deno_cond_f_elim _ e c2 c3 m); trivial.
  
  apply equiv_eq_compat_r with (d1 ++ [Assert !f] ++ d3 ++ d4); intros.

  rewrite deno_app_elim, deno_app_elim; apply mu_stable_eq.
  refine (ford_eq_intro _); intro m.
  rewrite deno_app_elim, deno_assert_elim.
  symmetry; rewrite deno_app_elim, deno_assert_elim.  
  rewrite eval_negb; case_eq (E.eval_expr f m); intro; [trivial | ].
  simpl negb; cbv iota.
  rewrite deno_app_elim, deno_app_elim, (deno_cond_f_elim _ f d2 d3 m); trivial.

  trivial.
 Qed.


 Section SPLIT_WHILE.

  Variables E1 E2 : env.

  Variables c1 c2 : cmd.
  
  Variables b1 b2 P1 P2 : E.expr T.Bool.
 
  Variables I : mem_rel.

  Variable i : Var.var T.Nat.

  Variable HI1 : implMR I (EP_eq_expr b1 b2).

  Variable HI2 : implMR I (EP_eq_expr P1 P2).
 
  Variable k : nat.

  Variable lam1 : nat -> R.

  Variable lam2 : R.

  Hypothesis Hlam1 : forall k, (1 <= lam1 k)%R. 
 
  Hypothesis Hlam2 : (1 <= lam2)%R. 

  Hypothesis H1 : forall j:nat, 
   eequiv 
   (I /-\ EP1 b1 /-\ EP1 (i =?= j) /-\ EP1 (!P1) )
   E1 (c1 ++ [ Assert !P1 ])
   E2 (c2 ++ [ Assert !P2 ]) 
   (I /-\ EP1 (i =?= S j) /-\ EP1 (!P1)) 
   (fun k => lam1 j) (fun k => 0).

  Hypothesis H2 : forall j:nat,
   eequiv 
   (I /-\ EP1 b1 /-\ EP1 (i =?= j) /-\ EP1 (!P1))
   E1 (c1 ++ [ Assert P1 ])
   E2 (c2 ++ [ Assert P2 ])
   (I /-\ EP1 (i =?= S j) /-\ EP1 P1) 
   (fun k => lam2) (fun k => 0).

  Hypothesis H3 : forall j:nat,
   equiv 
   ((I /-\ EP1 b1 /-\ EP1 (i =?= j)) /-\ EP1 P1)
   E1 c1 
   E2 c2 
   ((I /-\ EP1 (i =?= S j)) /-\ EP1 P1).

  (** 
     The next two hyptotheses could be replaced by
     Hypothesis H4 : equiv (I /-\ EP1 b1) E1 c1 E2 c2 I
  *)

  Hypothesis range_c1 : forall k (m:Mem.t k),
   EP k P1 m -> range (EP k P1) ([[c1]] E1 m).

  Hypothesis range_c2 : forall k (m:Mem.t k),
   EP k P2 m -> range (EP k P2) ([[c2]] E2 m).

  Lemma split_unroll_first : forall (n a:nat) lam,
   (forall k, 1 <= lam k)%R ->
   (forall k, ProdRR lam1 a n <= lam k)%R ->
   eequiv
   ((I /-\ EP1 (i =?= a)) /-\ ~- EP1 P1)
   E1 (unroll_while b1 (c1 ++ [Assert !P1]) n)
   E2 (unroll_while b2 (c2 ++ [Assert !P2]) n)
   I lam (fun k => 0).  
  Proof.
   induction n; intros a lam Hle Hge.
   apply eequiv_cond; trivial.
   eapply eequiv_weaken; [ | | | | apply eequiv_nil]; trivial.
   unfold implMR, andR; intuition.
   eapply eequiv_weaken; [ | | | | apply eequiv_nil]; trivial.
   unfold implMR, andR; intuition.
   unfold implMR, andR; intuition.
   apply HI1 in H; trivial.

   (* inductive case *)
   simpl.
   eapply eequiv_weaken with 
    (lam':=fun k => _) 
    (ep':=fun k => _);
    [ | | | | apply eequiv_cond]; trivial.
   intros; rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; auto; try fourier.
   apply ProdRR_ge_1; intros; trivial.

   2:eapply eequiv_weaken; [ | | | | apply eequiv_nil]; trivial.
   2:unfold implMR, andR; intuition.
   2:intro; apply ProdRR_ge_1; trivial.
   2:intros ? ? ? [ [? ?] ?]; apply HI1 in H; unfold EP_eq_expr in H; trivial.
   
   eapply eequiv_weaken with 
    (lam':=fun k => (lam1 a * ProdRR lam1 (S a) n)%R) 
    (ep:=fun k => 0) 
    (ep':=fun k => max (0 + _ ** 0) (0 + _ ** 0));
    [ | | | | eapply eequiv_seq with (Q':=(I /-\ EP1 (i =?= S a)) /-\ ~- EP1 P1) ].
   trivial.
   trivial.
   trivial.
   apply ford_le_intro; intro; apply max_le; rewrite multRU_0_r; auto.   
   intro; apply ProdRR_ge_1; auto.
   
   eapply eequiv_weaken; [ | | | | apply (H1 a)].
   unfold implMR, andR; intuition.
   apply is_true_negb in H5; trivial.   
   unfold implMR, andR; intuition.
   apply is_true_negb; trivial.
   trivial.
   trivial.

   apply (IHn (S a)).   
   intro; apply ProdRR_ge_1; trivial.
   trivial.
  Qed.

  Lemma split_unroll_last : forall (n a:nat) lam,
   (forall k, 1 <= lam k)%R ->
   eequiv 
   ((I /-\ EP1 (i =?= a)) /-\ EP1 P1)
   E1 (unroll_while b1 c1 n ++ [Assert P1])
   E2 (unroll_while b2 c2 n ++ [Assert P2])
   I lam (fun k => 0).  
  Proof.
   induction n; intros.

   eapply eequiv_weaken; 
    [ | | | | apply eequiv_seq with (Q':=I) (ep:=fun k => 0) (ep':=fun k => 0)
      (lam:=fun k => 1%R) (lam':=fun k => 1%R)].
   trivial.
   trivial.
   intros; rewrite Rmult_1_l; intuition.
   apply ford_le_intro; intros; apply max_le; 
    rewrite multRU_0_r, Uplus_zero_left; trivial.
   trivial.

   apply eequiv_cond; trivial. 
   eapply eequiv_weaken; [ | | | | apply eequiv_nil]; trivial.
   unfold implMR, andR; intuition.   
   eapply eequiv_weaken; [ | | | | apply eequiv_nil]; trivial.
   unfold implMR, andR; intuition.   
   
   intros ? ? ? [ [? _] _]; apply HI1; trivial.
   eapply eequiv_weaken; 
    [ | | | | apply equiv_eequiv; apply equiv_assert with (P:=I)]; trivial.
   unfold implMR, andR; intuition.
   apply HI2; trivial.
   unfold implMR, andR; intuition.

   (* inductive case *)
   simpl unroll_while.
   apply eequiv_case with (P':=EP1 b1); [trivial | | ].

   apply eequiv_eq_compat_l with 
    (c1 ++ unroll_while b1 c1 n ++ [Assert P1]).
   intros ? ? ? ? [ [? ?] ? ].
   symmetry; rewrite deno_app_elim, deno_cond_elim, H5, deno_app_elim; trivial.
   rewrite deno_app_elim.
   apply mu_stable_eq; refine (ford_eq_intro _); intro.
   symmetry; apply deno_app_elim.

   apply eequiv_eq_compat_r with 
    (c2 ++ unroll_while b2 c2 n ++ [Assert P2]).
   intros ? ? ? ? [ [ [? ?] ?] ? ].
   symmetry; rewrite deno_app_elim, deno_cond_elim.
   rewrite <-(HI1 H0), H6, deno_app_elim; trivial.
   rewrite deno_app_elim.
   apply mu_stable_eq; refine (ford_eq_intro _); intro.
   symmetry; apply deno_app_elim.

   eapply eequiv_weaken with (lam':=fun k => _) (ep':=fun k => _);
    [ | | | | eapply eequiv_seq; [ | apply equiv_eequiv, (H3 a) | apply IHn ]  ].
   unfold implMR, andR; intuition.
   trivial.
   intros; simpl.
   rewrite Rmult_1_l; trivial.
   apply ford_le_intro; intro; apply max_le; rewrite multRU_0_r; Usimpl; trivial.
   trivial.
   trivial.

   apply eequiv_eq_compat_l with [Assert P1].
   intros ? ? ? ? [ [ [? ?] ?] ? ].
   symmetry; rewrite deno_app_elim, deno_cond_elim.
   apply not_is_true_false in H6; rewrite H6, deno_nil_elim; trivial.

   apply eequiv_eq_compat_r with [Assert P2].
   intros ? m1 m2 f [ [ [? ?] ?] ? ].
   symmetry; rewrite deno_app_elim, deno_cond_elim.
   rewrite <-(HI1 H0).
   apply not_is_true_false in H6; rewrite H6, deno_nil_elim; trivial.

   eapply eequiv_weaken; 
    [ | | | | apply equiv_eequiv; apply equiv_assert with (P:=I)]; trivial.
   unfold implMR, andR; intros ? m1 m2 [ [ [? ?] ?] ?]; repeat split; trivial.
   apply HI2; trivial.
   unfold implMR, andR; intuition.
  Qed.

  Lemma split_unroll_second : forall (n a:nat) lam,
   (forall k, 1 <= lam k)%R ->
   (forall k, ProdRR lam1 a n * lam2 <= lam k)%R ->
   decMR I ->
   eequiv
   ((I /-\ EP1 (i =?= a)) /-\ ~- EP1 P1)
   E1 (unroll_while b1 c1 n ++ [Assert P1])
   E2 (unroll_while b2 c2 n ++ [Assert P2])
   I
   lam (fun k => 0).  
  Proof.
   induction n; intros.

   simpl unroll_while.
   eapply eequiv_weaken with
    (lam':=fun k => (1 * 1)%R)
    (ep':= fun k => max (0 + _) (0 + _)); 
    [ | | | | apply eequiv_seq with (I /-\ ~- EP1 P1)].
   trivial.
   trivial.
   intros; rewrite Rmult_1_l; trivial.
   apply ford_le_intro; intro; rewrite multRU_0_r, max_le; auto.
   trivial.

   apply eequiv_cond.
   trivial.
   eapply eequiv_weaken; [ | | | | apply eequiv_nil]; trivial.
   unfold implMR, andR; intuition.
   eapply eequiv_weaken; [ | | | | apply eequiv_nil]; trivial.
   unfold implMR, andR; intuition.
   intros ? ? ? [ [? _] _]; apply HI1; trivial.

   apply equiv_eequiv.
   eapply equiv_sub; [ | | apply equiv_assert with (P:=I)].
   intros ? ? ? [? ?]; split; [ | apply HI2 ]; trivial.
   unfold andR; intuition.
   
   (* Inductive case *)
   simpl unroll_while.
   apply eequiv_case with (EP1 b1).
   trivial.
   
   apply eequiv_eq_compat_l with
    (c1 ++ (unroll_while b1 c1 n ++ [Assert P1])).
   intros ? ? ? ? [ [ [? _] _] ?].
   rewrite deno_app_elim, deno_app_elim.
   rewrite deno_cond_t_elim; trivial.
   rewrite deno_app_elim.
   apply mu_stable_eq; refine (ford_eq_intro _); intros.
   rewrite deno_app_elim; trivial.

   apply eequiv_eq_compat_r with
    (c2 ++ (unroll_while b2 c2 n ++ [Assert P2])).
   intros ? ? ? ? [ [ [? _] _] ?].
   rewrite deno_app_elim, deno_app_elim.
   rewrite deno_cond_t_elim; trivial.
   rewrite deno_app_elim.
   apply mu_stable_eq; refine (ford_eq_intro _); intros.
   rewrite deno_app_elim; trivial.
   apply HI1 in H4.
   unfold EP_eq_expr in H4; rewrite <-H4; trivial.

   eapply eequiv_weaken with
    (lam':=fun k => Rmax (lam2 * ProdRR lam1 a (S n)) 
                         (ProdRR lam1 a (S n) * lam2) )
    (ep':=fun k => _) ;
    [ | | | | eapply eequiv_assert_app with P1 P2].
   trivial.
   trivial.
   intros; apply Rmax_case; trivial.
   rewrite Rmult_comm; trivial.
   trivial.
   intros; rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; trivial.
   fourier.
   fourier.
   apply ProdRR_ge_1; trivial.
   intros; rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; trivial.
   fourier.
   fourier.
   apply ProdRR_ge_1; trivial.
   
   auto.

   rewrite app_assoc, (app_assoc c2).
   eapply eequiv_weaken with
    (lam':=fun k => (lam2 * ProdRR lam1 (S a) n)%R)
    (ep':=fun k => max (0 + _) (0 + _));
    [ | | | | apply eequiv_seq with (I /-\ EP1 (i =?= S a) /-\ EP1 P1) ].
   trivial.
   trivial.
   intros; apply Rmult_le_compat; trivial.
   fourier.
   rewrite <-ProdRR_ge_1; trivial; fourier.

   simpl.
   rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; trivial.
   fourier.
   rewrite <-ProdRR_ge_1; trivial; fourier.
  
   apply ford_le_intro; intro; apply max_le; 
    rewrite multRU_0_r, Uplus_zero_left; trivial.
   intro; apply ProdRR_ge_1; trivial.
   
   eapply eequiv_weaken; [ | | | | apply (H2 a)].
   unfold implMR, andR; intuition.
   apply not_is_true_false in H7.
   unfold EP1; rewrite eval_negb, H7; trivial.
   unfold implMR, andR; intuition.
   trivial.
   trivial.

   eapply eequiv_weaken; [ | | | | apply (split_unroll_last n (S a))].
   unfold implMR, andR; intuition.
   trivial.
   intros; apply Rle_refl.
   trivial.
   intros; simpl; apply ProdRR_ge_1; trivial.

   rewrite app_assoc, (app_assoc c2).
   eapply eequiv_weaken with
    (lam':=fun k => (lam1 a * (ProdRR lam1 (S a) n * lam2))%R)
    (ep':=fun k => max (0 + _) (0 + _));
    [ | | | | apply eequiv_seq with (I /-\ EP1 (i =?= S a) /-\ EP1 (!P1)) ].
   trivial.
   trivial.
   intros; simpl.
   rewrite <-Rmult_assoc, Rmult_comm; trivial.
   apply ford_le_intro; intro; apply max_le; 
    rewrite multRU_0_r, Uplus_zero_left; trivial.
   intros; rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; trivial.
   fourier.
   fourier.
   apply ProdRR_ge_1; trivial.

   eapply eequiv_weaken;
    [ | | | | apply (H1 a)].
   unfold implMR, andR; intuition.
   apply not_is_true_false in H7.
   unfold EP1; rewrite eval_negb, H7; trivial.
   unfold implMR, andR; intuition.
   trivial.
   trivial.

   eapply eequiv_weaken
    with (lam':=fun k => (ProdRR lam1 (S a) n * lam2)%R); 
     [ | | | | apply (IHn (S a))].
   unfold implMR, andR; intuition.
   unfold EP1 in H7; rewrite eval_negb in H7.
   apply not_is_true_false.
   apply is_true_negb in H7; trivialb.
   trivial.
   intros; trivial.
   trivial.
   intros; rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; trivial.
   fourier.
   fourier.
   apply ProdRR_ge_1; trivial.
   trivial.

   auto.

   apply eequiv_eq_compat_l with [Assert P1].
   intros ? ? ? ? [ [ [? ?] ? ] ?].
   rewrite deno_assert_elim, deno_app_elim, deno_cond_elim.
   apply not_is_true_false in H7; rewrite H7.
   apply not_is_true_false in H6; rewrite H6.
   rewrite deno_nil_elim, deno_assert_elim.
   rewrite H6; trivial.

   apply eequiv_eq_compat_r with [Assert P2].
   intros ? ? ? ? [ [ [? ?] ? ] ?].
   rewrite deno_assert_elim, deno_app_elim, deno_cond_elim.
   rewrite <-(HI1 H4).
   rewrite <-(HI2 H4).
   apply not_is_true_false in H7; rewrite H7.
   apply not_is_true_false in H6; rewrite H6.
   rewrite deno_nil_elim, deno_assert_elim.
   rewrite <-(HI2 H4), H6; trivial.
   
   eapply eequiv_weaken; [ | | | | apply equiv_eequiv]; trivial.
   eapply equiv_sub; [ | | apply equiv_assert with (P:=I)].
   intros ? ? ? [ [ [? ?] ?] _].
   split; trivial.
   apply HI2; trivial.
   unfold andR; intuition.
  Qed.

  Lemma assert_contradiction : forall k b c e n E (m:Mem.t k) f,
   (forall m, EP k e m -> range (EP k e) ([[c]] E m)) ->
   EP k e m ->
   mu ([[ unroll_while b c n ++ [Assert !e] ]] E m) f == 0.
  Proof.
   induction n; intros.
   
   simpl unroll_while.
   rewrite deno_app_elim, deno_cond_elim.
   case (E.eval_expr b m);
    rewrite deno_nil_elim, deno_assert_elim, eval_negb, H0; trivial.

   simpl unroll_while.
   rewrite deno_app_elim, deno_cond_elim.
   case (E.eval_expr b m).
   rewrite deno_app_elim.
   symmetry; apply H; trivial.
   intros.
   rewrite <-deno_app_elim.
   symmetry; apply IHn;  trivial.
 
   rewrite deno_nil_elim, deno_assert_elim.
   rewrite eval_negb, H0; trivial.
  Qed.

  Lemma push_assert : forall k b c e n E (m:Mem.t k) f,
   (forall m, EP k e m -> range (EP k e) ([[c]] E m)) ->
   EP k (!e) m ->
   mu ([[ unroll_while b (c ++ [Assert !e]) n ]] E m) f ==
   mu ([[ unroll_while b c n ++ [Assert !e] ]] E m) f.
  Proof.
   clear; induction n; intros.
   simpl unroll_while.
   rewrite deno_cond_elim.
   symmetry; rewrite deno_app_elim, deno_cond_elim.
   case (E.eval_expr b m);
    rewrite deno_nil_elim, deno_nil_elim, deno_assert_elim, H0; trivial.
 
   simpl unroll_while.
   rewrite deno_cond_elim.
   symmetry; rewrite deno_app_elim, deno_cond_elim.
   case (E.eval_expr b m).
   2:rewrite deno_nil_elim, deno_nil_elim, deno_assert_elim, H0; trivial.

   rewrite deno_app_elim, deno_app_elim, deno_app_elim.
   transitivity 
    (mu ([[c]] E m)
     (fun m' =>
      if EP k (!e) m' then 
       mu ([[ unroll_while b c n ]] E m')
           (fun m'' => mu ([[ [Assert !e] ]] E m'') f)
    else 0)).
   apply mu_stable_eq.
   refine (ford_eq_intro _); intro m'.
   case_eq (EP k (!e) m'); intro He.
   trivial.
   rewrite <-deno_app_elim.
   apply assert_contradiction.
   trivial.
   unfold EP in He; rewrite eval_negb in He.
   apply negb_false_iff in He; trivial.

   apply mu_stable_eq.
   refine (ford_eq_intro _); intro m'.
   rewrite deno_assert_elim.
   unfold EP.
   case_eq (@E.eval_expr k T.Bool (!e) m').
   symmetry.
   rewrite <-deno_app_elim.
   apply IHn.
   trivial.
   trivial.
   trivial.
  Qed.

  Lemma split_unroll_le_lift : forall (n a:nat) lam,
   (forall k, 1 <= lam k)%R ->
   (forall k j, (j <= n)%nat -> (ProdRR lam1 a j * lam2 <= lam k)%R) ->
   decMR I ->
   eequiv ((I /-\ EP1 (i =?= a)) /-\ ~- EP1 P1)
   E1 (unroll_while b1 c1 n ++ [Assert !b1])
   E2 (unroll_while b2 c2 n ++ [Assert !b2])
   I
   lam (fun k => 0).  
  Proof.
   intros n a lam HI Hge Hle.
   eapply eequiv_seq_weaken with 
    (lam1:=fun k => lam k) (ep1:=fun _ => 0) 
    (lam2:=fun k => 1%R)   (ep2:=fun _ => 0).
   trivial.
   intros; rewrite Rmult_1_r; trivial.
   intros; apply max_le; rewrite multRU_0_r, Uplus_zero_left; trivial.

   eapply eequiv_weaken with (lam':=fun k => _);
    [ | | | | apply eequiv_assert_join with (e1:=P1) (e2:=P2)]; trivial.
   intro; rewrite Rmax_left; trivial.   

   apply (split_unroll_second n a lam); trivial.
   auto.

   apply eequiv_eq_compat_l with
    (unroll_while b1 (c1 ++ [Assert !P1]) n).
   intros.
   apply push_assert.
   intros; apply range_c1; trivial.
   destruct H as [_ ?].
   apply not_is_true_false in H.
   unfold EP; rewrite eval_negb; trivial.
   rewrite H; trivial.

   apply eequiv_eq_compat_r with
    (unroll_while b2 (c2 ++ [Assert !P2]) n).
   intros.
   apply push_assert.
   intros; apply range_c2; trivial.
   destruct H as [ [? _] ?].
   apply HI2 in H.
   apply not_is_true_false in H0.
   unfold EP; rewrite eval_negb; trivial.
   unfold EP_eq_expr in H; rewrite H in H0; rewrite H0; trivial.

   apply split_unroll_first; trivial.
 
   intro; transitivity (ProdRR lam1 a n * lam2)%R; [ | auto].
   rewrite <-Rmult_1_r at 1. 
   apply Rmult_le_compat; [ | fourier | auto | fourier].
   rewrite <-ProdRR_ge_1; [fourier | auto].
   auto.
  
   apply equiv_eequiv. 
   eapply equiv_sub; [ | | apply equiv_assert with (P:=I)].
   intros; split; trivial.
   rewrite eval_negb, eval_negb.
   rewrite (HI1 H); trivial.
   unfold andR; intuition.
  Qed.
 
  Lemma eequiv_while_split : forall lam (a n:nat),
   (forall k, 1 <= lam k)%R ->
   (forall k j, (j <= n)%nat -> ProdRR lam1 a j * lam2 <= lam k)%R ->
   decMR I ->
   (forall k (m1 m2:Mem.t k), 
    I m1 m2 -> 
    [[ [while b1 do c1] ]] E1 m1 == 
    drestr ([[ unroll_while b1 c1 n ]] E1 m1) (negP (EP k b1)) /\
    [[ [while b2 do c2] ]] E2 m2 == 
    drestr ([[ unroll_while b2 c2 n ]] E2 m2) (negP (EP k b2))) ->
   eequiv
    (I /-\ EP1 (i =?= a) /-\ EP1 (!P1))
    E1 [ while b1 do c1 ]
    E2 [ while b2 do c2 ]
    (I /-\ EP1 (!b1))
    lam (fun k => 0).
  Proof.
   intros.
   apply eequiv_eq_compat_l with [while b1 do c1; Assert !b1].
   intros ? ? ? ? [? [? ?] ].
   rewrite deno_cons_elim, Mlet_simpl.
   symmetry; rewrite deno_while_restr_elim.
   apply mu_stable_eq.
   refine (ford_eq_intro _); intros ?.
   rewrite deno_assert_elim, eval_negb; case (E.eval_expr b1 n0); trivial.

   apply eequiv_eq_compat_r with [while b2 do c2; Assert !b2].
   intros ? ? ? ? [? [? ?] ].
   rewrite deno_cons_elim, Mlet_simpl.
   symmetry; rewrite deno_while_restr_elim.
   apply mu_stable_eq.
   refine (ford_eq_intro _); intros ?.
   rewrite deno_assert_elim, eval_negb; case (E.eval_expr b2 n0); trivial.
 
   repeat match goal with 
    |- context [ [?i1; ?c1] ] => change [i1; c1] with ([i1] ++ [c1])
   end.
   eapply eequiv_weaken with
    (lam':=fun k => (lam k * 1)%R)
    (ep' :=fun k => max (0 + _) (0 + _));
    [ | | | | apply eequiv_seq with I ].
   trivial.
   trivial.
   intro; rewrite Rmult_1_r; trivial.
   apply ford_le_intro; intros; apply max_le; 
    rewrite multRU_0_r, Uplus_zero_left; trivial.
   trivial.

   unfold eequiv; intros.
   destruct (@split_unroll_le_lift n a lam H H0 X k0 m1 m2) as [d Hd].
   exists d; intros [? [? ?] ].
   destruct (H4 _ _ _ H5).
   eapply le_lift_eq_compat.
   reflexivity.
   symmetry; apply H8.
   symmetry; apply H9.
   reflexivity.
   reflexivity.
   
   refine (le_lift_eq_compat _ _ _ _ _ (Hd _)); trivial.

   apply eq_distr_intro; intro f.
   unfold drestr; rewrite deno_app_elim, Mlet_simpl.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
   rewrite deno_assert_elim, eval_negb.
   unfold negP, EP; case (E.eval_expr b1 m'); trivial.

   apply eq_distr_intro; intro f.
   unfold drestr; rewrite deno_app_elim, Mlet_simpl.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
   rewrite deno_assert_elim, eval_negb.
   unfold negP, EP; case (E.eval_expr b2 m'); trivial.

   unfold andR; intuition.
   apply is_true_negb; unfold EP1 in H7; rewrite eval_negb in H7; trivial.

   apply equiv_eequiv.
   eapply equiv_sub; [ | | apply equiv_assert].
   intros; split.
   eexact H5.
   rewrite eval_negb, eval_negb; apply HI1 in H5; unfold EP_eq_expr in H5.
   rewrite H5; trivial.
   unfold andR; intuition.  
  Qed.

 End SPLIT_WHILE.

End Sym_Logic.



Section Asymm_Logic.

 Definition eequiva (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) 
  (lam:nat -> R) (ep:nat-o>U) :=
  forall k m1 m2,
   sig (fun d => 
    P k m1 m2 -> 
    le_lift_asym (Q k) d ([[c1]] E1 m1) ([[c2]] E2 m2) (lam k) (ep k)).

 Lemma equiv_eequiva : forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel),
  equiv P E1 c1 E2 c2 Q -> eequiva P E1 c1 E2 c2 Q (fun _ => R1) (fzero _).
 Proof.
  unfold eequiva, equiv; intros.
  apply constructive_indefinite_description.
  destruct (H k) as (d,Hd).
  exists (d m1 m2); intros. 
  apply (proj2 (le_lift_asym_lift _ _ _ _)); auto.
 Qed.

 Lemma eequiva_deno : forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) lam ep,
  eequiva P E1 c1 E2 c2 Q lam ep ->
  forall k (f g : Mem.t k -> U),
  (forall m1 m2 : Mem.t k, Q k m1 m2 -> f m1 <= g m2) ->
  forall m1 m2 : Mem.t k,
  P k m1 m2 -> 
  d_expr_asym ([[ c1 ]] E1 m1) ([[ c2 ]] E2 m2) (lam k) f g <= (ep k).
 Proof.
  unfold eequiva; intros.
  destruct (X k m1 m2) as [d Hd]; trivial.
  apply le_lift_asym_elim with (Q k) d; auto.  
 Qed.     

 Lemma eequiva_sdeno : forall c1 E1 c2 E2 (P Q:mem_rel) ep ep' lam lam'
  k (d1 d2 : Distr(Mem.t k)),
  (forall k, 1 <= lam' k)%R ->
  is_Discrete d1 ->
  is_Discrete d2 ->
  eequiva P E1 c1 E2 c2 Q lam' ep' ->
  (exists d, le_lift_asym (@P k) d d1 d2 (lam k) (ep k)) ->
  forall f g,
  (forall m1 m2 : Mem.t k, Q k m1 m2 -> f m1 <= g m2) ->
  d_expr_asym (Mlet d1 ([[c1]] E1)) (Mlet d2 ([[c2]] E2)) (lam k * lam' k) f g <= 
  ep k + lam k ** ep' k.
 Proof.
  unfold eequiva; intros; destruct H0 as [d Hd].
  apply le_lift_asym_elim with (S:=Q k) 
   (d:=Mlet d (fun mm => proj1_sig (X1 _ (fst mm) (snd mm)))); trivial.
  apply le_lift_asym_Mlet with 
   (P k) (fun ab ab' => mem_eqU (fst ab) (fst ab') * mem_eqU (snd ab) (snd ab')).
  apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
  refine (le_lift_asym_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) X X0 Hd).
  trivial.
  trivial.
  intros m1 m2 Hm; simpl; destruct (X1 k m1 m2) as (d', Hd'); auto.
 Qed.

 Lemma eequiva_weaken : 
  forall P E1 c1 E2 c2 Q lam ep P' Q' (lam':nat -> R) (ep':nat -o> U),
   implMR P P' ->
   implMR Q' Q ->
   (forall x, (lam' x <= lam x)%R) ->
   ep' <= ep ->
   eequiva P' E1 c1 E2 c2 Q' lam' ep' ->
   eequiva P  E1 c1 E2 c2 Q  lam ep.
 Proof.
  unfold eequiva; intros.
  destruct (X _ m1 m2) as (d,Hd); clear X.
  exists d.
  intros Hm; apply le_lift_asym_weaken with (Q' k) (lam' k) (ep' k); auto.
 Qed.

 Lemma eequiva_eq_compat_l : forall (P Q:mem_rel) E1 E2 c1 c1' c2 lam ep,
  (forall k (m1 m2:Mem.t k) f, 
   P k m1 m2 -> mu ([[c1]] E1 m1) f == mu ([[c1']] E1 m1) f) ->
  eequiva P E1 c1  E2 c2  Q lam ep ->
  eequiva P E1 c1' E2 c2 Q lam ep.
 Proof.
  intros P Q E1 E2 c1 c1' c2 lam ep Heq Hequiv k m1 m2.
  destruct (Hequiv k m1 m2) as [d Hd].
  exists d; intros.
  assert (X:=fun f => Heq k m1 m2 f H).
  apply eq_distr_intro in X.
  rewrite <-X; auto.
 Qed. 

 Lemma eequiva_eq_compat_r : forall (P Q:mem_rel) E1 E2 c1 c2 c2' lam ep,
  (forall k (m1 m2:Mem.t k) f, 
   P k m1 m2 -> mu ([[c2]] E2 m2) f == mu ([[c2']] E2 m2) f) ->
  eequiva P E1 c1 E2 c2  Q lam ep ->
  eequiva P E1 c1 E2 c2' Q lam ep.
 Proof.
  intros P Q E1 E2 c1 c2 c2' lam ep Heq Hequiv k m1 m2.
  destruct (Hequiv k m1 m2) as [d Hd].
  exists d; intros.
  assert (X:=fun f => Heq k m1 m2 f H).
  apply eq_distr_intro in X.
  rewrite <-X; auto.
 Qed. 

 Lemma eequiva_trueR : forall (P:mem_rel) E1 c1 E2 c2 (lam:nat -> R) ep1 ep2,
  (forall k, 1 <= lam k)%R ->
  (forall k (m1 m2:Mem.t k), P _ m1 m2 ->
   mu ([[c1]] E1 m1) (fone _) <= ep1 k /\
   ep2 k <=  mu ([[c2]] E2 m2) (fone _)) ->
  eequiva P E1 c1 E2 c2 trueR lam 
  (fun k => ([1-] (lam k ** (ep2 k))) * (ep1 k)).
 Proof.
  unfold eequiva; intros.
  exists (prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2)).
  intros Hm.
  eapply le_lift_asym_weaken; [ | | | apply 
   (@le_lift_asym_true _ _ ([[c1]] E1 m1) ([[c2]] E2 m2) (lam k)) ]; trivial.
  apply Umult_le_compat.
   apply Uinv_le_compat, multRU_le_compat. 
     transitivity 1%R; auto with real.
     trivial.
     apply (proj2 (H0 _ _ _ Hm)).
   apply (proj1 (H0 _ _ _ Hm)).
 Qed.


 Lemma eequiva_trueR_lossless : forall (P:mem_rel) E1 c1 E2 c2,
  lossless E2 c2 -> 
  eequiva P E1 c1 E2 c2 trueR (fun _ => R1) (fzero _).
 Proof.
  intros.
  eapply eequiva_weaken; [ | | | |  apply (eequiva_trueR P E1 c1 E2 c2 
    (fun _ => 1%R) (fone _) (fone _)) ]; trivial.
  unfold fzero, fone; refine (ford_le_intro _); intro k;
    multRU_simpl; repeat Usimpl; trivial.
  unfold fone; split; auto.
 Qed.

 Lemma eequiva_falseR : forall E1 c1 E2 c2 Q,
  eequiva falseR E1 c1 E2 c2 Q (fun _ => R1) (fzero _).
 Proof.
  unfold eequiva; intros.
  exists (distr0 _).
  unfold falseR; intros H; tauto.
 Qed.

 Hint Resolve eequiva_falseR.


 Lemma eequiva_case : forall (P P':mem_rel) E1 c1 E2 c2 Q lam ep,
  decMR P' ->
  eequiva (P /-\ P') E1 c1 E2 c2 Q lam ep ->
  eequiva (P /-\ ~-P') E1 c1 E2 c2 Q lam ep ->
  eequiva P E1 c1 E2 c2 Q lam ep. 
 Proof.
  unfold andR, notR, eequiva; intros.
  destruct (X0 _ m1 m2) as (dt,Hdt); destruct (X1 _ m1 m2) as (df,Hdf).
  destruct (X k m1 m2); [ exists dt | exists df ]; auto.
 Qed.

 Lemma eequiva_nil : forall P E1 E2, 
  eequiva P E1 (@nil I.instr) E2 (@nil I.instr) P (fun _ => R1) (fzero _).
 Proof.
  unfold eequiva; intros.
  exists (Munit (m1, m2)); intros.
  rewrite deno_nil, deno_nil.
  apply (le_lift_asym_Munit _ _ _ (Rle_refl _) H).
 Qed.

 Lemma eequiva_seq : forall (P:mem_rel) E1 c1 E2 c2 Q' lam ep Q c1' c2' lam' ep',
  (forall k, 1 <= lam' k)%R ->
  eequiva P E1 c1  E2 c2 Q' lam ep ->
  eequiva Q' E1 c1' E2 c2' Q lam' ep' ->
  eequiva P E1 (c1 ++ c1') E2 (c2 ++ c2') Q (fun k => lam k * lam' k)%R 
  (fun k => ep k + lam k ** ep' k).
 Proof.
  unfold eequiva; intros.
  destruct (X _ m1 m2) as (d, Hd).
  exists (Mlet d (fun mm => proj1_sig (X0 _ (fst mm) (snd mm)))). 
  intro Hm.
  rewrite deno_app, deno_app.
  apply le_lift_asym_Mlet with (Q' k)
   (fun ab ab' => mem_eqU (fst ab) (fst ab') * mem_eqU (snd ab) (snd ab')).
  apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
  refine (le_lift_asym_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) 
   (sem_discr _ _ _) (sem_discr _ _ _) (Hd Hm)).
  trivial.
  auto.
  intros m1' m2' Hm'; simpl; destruct (X0 _ m1' m2') as (d', Hd'); auto.
 Qed.

 Lemma eequiva_frame : forall (P Q I:mem_rel) E1 c1 E2 c2 del ep,
  (forall k (m1 m2:Mem.t k), 
   I _ m1 m2 -> range (prodP (@I k)) (prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2))) ->
  eequiva P E1 c1 E2 c2 Q del ep ->
  eequiva (P /-\ I) E1 c1 E2 c2 (Q /-\ I) del ep.
 Proof.
  intros; intros k m1 m2.
  destruct (X _ m1 m2) as [d Hd].
  exists d; intros (HP,HI).
  pose proof (le_lift_asym_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)
   (sem_discr _ _ _) (sem_discr _ _ _) (Hd HP)) as Hd_discr.
  destruct (Hd HP); clear Hd.
  constructor; trivial. clear le_lam_asym le_d_asym.
  unfold prodP, andR; apply (range_discr_strengthen Hd_discr _
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)) le_r_asym). 
  apply (range_discr_intro _ Hd_discr _
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k))).
  intros mm Hmm.
  apply (range_discr_elim _ 
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)) (H _ _ _ HI)).
  intro H'; elim Hmm.
  assert (Haux: mu ([[ c1 ]] E1 m1) (fun m =>  mem_eqU (fst mm) m) *
   mu ([[ c2 ]] E2 m2) (fun m =>  mem_eqU (snd mm) m) == 0); [ | clear H' ].
  unfold prod_distr in H'; rewrite Mlet_simpl in H'; simpl in H'.
  rewrite Umult_sym, <-(mu_stable_mult (([[ c1 ]]) E1 m1) 
   (mu ([[ c2 ]] E2 m2) (fun m =>  mem_eqU (snd mm) m))), H'.
  apply mu_stable_eq; unfold fmult; refine (ford_eq_intro _); intro m.
  rewrite Umult_sym; symmetry.
  apply (mu_stable_mult (([[ c2 ]]) E2 m2) (mem_eqU (fst mm) m)).
  symmetry; apply Ule_zero_eq;  unfold Mfst, Msnd in *.
  apply (Ueq_orc ( mu ([[ c1 ]] E1 m1) (fun m =>  mem_eqU (fst mm) m)) 0); 
   [ auto | | ]; intro Hc1.
  rewrite <-Hc1, <-le_p1_asym, Mlet_simpl.
  apply mu_monotonic; refine (ford_le_intro _); intro m'; auto.
  rewrite (Umult_zero_simpl_right (Oeq_sym Haux) (neq_sym Hc1)), 
   <-le_p2_asym, Mlet_simpl.
  apply mu_monotonic; refine (ford_le_intro _); intro m'; auto.
 Qed.
 
 Lemma eequiva_range : forall (P Q I:mem_rel) E1 c1 E2 c2 del ep,
  (forall k (m1 m2:Mem.t k), 
   P k m1 m2 ->
   range (prodP (@I k)) (prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2))) ->
  eequiva P E1 c1 E2 c2 Q del ep ->
  eequiva P E1 c1 E2 c2 (Q /-\ I) del ep.
 Proof.
  intros; intros k m1 m2.
  destruct (X _ m1 m2) as [d Hd].
  exists d; intros HP.
  pose proof (le_lift_asym_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)
   (sem_discr _ _ _) (sem_discr _ _ _) (Hd HP)) as Hd_discr.
  destruct (Hd HP); clear Hd.
  constructor; trivial; clear le_lam_asym le_d_asym.
  unfold prodP, andR; apply (range_discr_strengthen Hd_discr _
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)) le_r_asym). 
  apply (range_discr_intro _ Hd_discr _
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k))).
  intros mm Hmm.
  eapply (range_discr_elim _ 
   (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)) (H k _ _ HP)).
  intro H'; elim Hmm.
  assert (Haux: mu ([[ c1 ]] E1 m1) (fun m =>  mem_eqU (fst mm) m) *
   mu ([[ c2 ]] E2 m2) (fun m =>  mem_eqU (snd mm) m) == 0); [ | clear H' ].
  unfold prod_distr in H'; rewrite Mlet_simpl in H'; simpl in H'.
  rewrite Umult_sym, <-(mu_stable_mult (([[ c1 ]]) E1 m1) 
   (mu ([[ c2 ]] E2 m2) (fun m =>  mem_eqU (snd mm) m))), H'.
  apply mu_stable_eq; unfold fmult; refine (ford_eq_intro _); intro m.
  rewrite Umult_sym; symmetry.
  apply (mu_stable_mult (([[ c2 ]]) E2 m2) (mem_eqU (fst mm) m)).
  symmetry; apply Ule_zero_eq;  unfold Mfst, Msnd in *.
  apply (Ueq_orc ( mu ([[ c1 ]] E1 m1) (fun m =>  mem_eqU (fst mm) m)) 0); 
   [ auto | | ]; intro Hc1.
  rewrite <-Hc1, <-le_p1_asym, Mlet_simpl.
  apply mu_monotonic; refine (ford_le_intro _); intro m'; auto.
  rewrite (Umult_zero_simpl_right (Oeq_sym Haux) (neq_sym Hc1)).
  rewrite <-le_p2_asym, Mlet_simpl.
  apply mu_monotonic; refine (ford_le_intro _); intro m'; auto.
 Qed.

 Lemma eequiva_range_l : forall (P Q:mem_rel) I E1 c1 E2 c2 del ep,
  (forall k (m1 m2:Mem.t k), P k m1 m2 -> range (@I k) ([[c1]] E1 m1)) ->
  eequiva P E1 c1 E2 c2 Q del ep ->
  eequiva P E1 c1 E2 c2 (Q /-\ (fun k m1 m2 => I k m1)) del ep.
 Proof.
  intros; apply eequiva_range; [ | trivial].
  intros k m1 m2 HP f Hf; simpl.
  apply (H k m1 m2 HP); intros.
  transitivity (mu ([[c2]] E2 m2) (fzero _)).
  symmetry; apply mu_zero.
  apply mu_stable_eq; refine (ford_eq_intro _); intro.
  unfold fzero; apply Hf; unfold prodP; trivial.
 Qed.

 Lemma eequiva_range_r : forall (P Q:mem_rel) I E1 c1 E2 c2 del ep,
  (forall k (m1 m2:Mem.t k), P k m1 m2 -> range (@I k) ([[c2]] E2 m2)) ->
  eequiva P E1 c1 E2 c2 Q del ep ->
  eequiva P E1 c1 E2 c2 (Q /-\ (fun k m1 m2 => I k m2)) del ep.
 Proof.
  intros; apply eequiva_range; [ | trivial].
  intros k m1 m2 HP.
  pose proof  (is_Discrete_commute _ (@mem_eqU_spec k)
  (sem_discr E2 c2 m2) ([[c1]] E1 m1)) as H'; unfold prod_comm in H'.
  rewrite H'; clear H'.
  intros f Hf; rewrite Mlet_simpl.
  refine (H k m1 m2 HP _ _); intros.
  rewrite <-(mu_zero ([[c1]] E1 m1)), Mlet_simpl. 
  apply mu_stable_eq; refine (ford_eq_intro _); intro.
  unfold fzero; simpl; apply Hf; unfold prodP; trivial.
 Qed.

 Lemma eequiva_inv_Modify : forall (X1 X2 M1 M2:Vset.t) 
  (P Q I:mem_rel) (E1:env) (c1:cmd) (E2:env) (c2:cmd) del ep,
  (forall k, 1 <= del k)%R ->
  depend_only_rel I X1 X2 ->
  Modify E1 M1 c1 ->
  Modify E2 M2 c2 ->
  Vset.disjoint X1 M1 -> 
  Vset.disjoint X2 M2 -> 
  eequiva P E1 c1 E2 c2 Q del ep ->
  eequiva (P /-\ I) E1 c1 E2 c2 (Q /-\ I) del ep.
 Proof.
  intros.
  apply eequiva_frame; trivial.
  intros k m1 m2 HI f Hf.
  unfold prod_distr; rewrite Mlet_simpl.
  rewrite (Modify_deno_elim H1).
  rewrite <-(mu_zero ([[ c1 ]] E1 m1)); apply mu_stable_eq; 
   unfold fzero; refine (ford_eq_intro _); intro m.
  rewrite Mlet_simpl, (Modify_deno_elim H2).
  rewrite <-(mu_zero ([[ c2 ]] E2 m2)); apply mu_stable_eq; 
   unfold fzero; refine (ford_eq_intro _); intro m'.
  rewrite Munit_eq.
  apply Hf; unfold prodP; simpl.
  refine (H0 _ _ _ _ _ _ _ HI);
   apply req_mem_sym; apply req_mem_update_disjoint; trivial.
 Qed.

 Lemma eequiva_seq_weaken:
  forall E1 E2 c1 c2 c1' c2' (P:mem_rel) Q Q' lam1 ep1 lam2 ep2 lam ep,
   (forall k, 1 <= lam2 k)%R ->
   (forall k, lam1 k * lam2 k <= lam k)%R ->
   (forall k, ep1 k + lam1 k ** ep2 k <= ep k) ->
   eequiva P  E1 c1  E2 c2  Q' lam1 ep1 ->
   eequiva Q' E1 c1' E2 c2' Q  lam2 ep2 ->
   eequiva P E1 (c1 ++ c1') E2 (c2 ++ c2') Q lam ep.
 Proof.
  intros.
  eapply eequiva_weaken with (P':=P) (Q':=Q) (lam':=fun k => _) (ep':=fun k => _);
   [ | | | | apply eequiva_seq with (Q':=Q')]; auto.
 Qed.

 Lemma eequiva_seq_equiv : forall E1 c1 c1' E2 c2 c2' P Q' Q lam ep,
  (forall k : nat, (1 <= lam k)%R) ->
  eequiva P  E1 c1  E2 c2  Q' lam ep ->
  equiv  Q' E1 c1' E2 c2' Q ->
  eequiva P  E1 (c1++c1') E2 (c2++c2') Q lam ep.
 Proof.
  intros.
  eapply eequiva_weaken with (P':=P) (Q':=Q);  
   [ | | | | eapply eequiva_seq with  (lam' := fun _ => R1) 
    (ep':= fun _ => D0) (lam:= lam) (ep := ep) (Q':= Q') ]; trivial.
  auto with real. 
  simpl; intro; repeat multRU_simpl; repeat Usimpl; auto.
  apply (equiv_eequiva H0).
 Qed.

 Lemma equiv_seq_eequiva : forall E1 c1 c1' E2 c2 c2' P Q' Q lam ep,
  (forall k : nat, (1 <= lam k)%R) ->
  equiv P  E1 c1  E2 c2  Q' ->
  eequiva Q' E1 c1' E2 c2' Q lam ep ->
  eequiva P E1 (c1++c1') E2 (c2++c2') Q lam ep.
 Proof.
  intros.
  eapply eequiva_weaken with (P':=P) (Q':=Q);
   [ | | | | eapply eequiva_seq with  (lam := fun _ => R1) 
    (ep:= fun _ => D0) (lam':= lam) (ep' := ep) (Q':= Q') ]; trivial.
  auto with real. 
  simpl; intro; repeat multRU_simpl; repeat Usimpl; auto.
  apply (equiv_eequiva H0).
 Qed.

 Lemma eequiva_cond_l : forall P E1 e c c' E2 c2 Q lam ep,
  eequiva (P /-\ EP1 e) E1 c E2 c2 Q lam ep ->
  eequiva (P /-\ ~- EP1 e) E1 c' E2 c2 Q lam ep ->
  eequiva P E1 [If e then c else c'] E2 c2 Q lam ep.
 Proof.
  unfold eequiva, andR, notR, EP1, is_true.
  intros P E3 e1 c c' E4 c2 Q lam ep Ht Hf k m1 m2.
  case_eq (E.eval_expr e1 m1); intro Heq.
  destruct (Ht _ m1 m2) as (dt,Hdt).
  exists dt; intro Hm.
  rewrite deno_cond, Heq; auto.

  destruct (Hf _ m1 m2) as (df,Hdf). 
  exists df; intro Hm. 
  rewrite deno_cond, Heq; auto.
  apply Hdf; split; trivial.
  apply not_is_true_false; trivial.
 Qed.

 Lemma eequiva_cond_r : forall P E1 c1 E2 e c c' Q lam ep,
  eequiva (P /-\ EP2 e) E1 c1 E2 c Q lam ep ->
  eequiva (P /-\ ~- EP2 e) E1 c1 E2 c' Q lam ep ->
  eequiva P E1 c1 E2 [If e then c else c'] Q lam ep.
 Proof.
  unfold eequiva, andR, notR, EP2, is_true.
  intros P E3 c c' e E4 c2 Q lam ep Ht Hf k m1 m2.
  case_eq (E.eval_expr e m2); intro Heq.
  destruct (Ht _ m1 m2) as (dt,Hdt).
  exists dt; intro Hm; rewrite deno_cond, Heq; auto.
  destruct (Hf _ m1 m2) as (df,Hdf).
  exists df; intro Hm. rewrite deno_cond, Heq.
  apply Hdf; rewrite Heq; auto using diff_false_true.
 Qed.

 Lemma eequiva_cond : 
  forall P Q E1 (e1:E.expr T.Bool) c1 c2 E2 (e2:E.expr T.Bool) c3 c4 lam ep,
   (forall k, 1 <= lam k)%R ->
   eequiva (P /-\ (EP1 e1 /-\ EP2 e2)) E1 c1 E2 c3 Q lam ep ->
   eequiva (P /-\ (~- EP1 e1 /-\ ~- EP2 e2)) E1 c2 E2 c4 Q lam ep ->
   (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
   eequiva P E1 [If e1 then c1 else c2] E2 [If e2 then c3 else c4] Q lam ep.
 Proof.
  intros; apply eequiva_cond_l; apply eequiva_cond_r.
  eapply eequiva_weaken with (5:=X); auto with real; simplMR; trivial.
  apply eequiva_weaken with falseR Q (fun _ => R1) (fzero _); auto; unfold EP1, EP2.
  intros k m1 m2 ((H2, H3), H4); apply H4; erewrite <-H0; eauto. 
  apply eequiva_weaken with falseR Q  (fun _ => R1) (fzero _); 
   auto; unfold EP1, EP2.
  intros k m1 m2 ((H2, H3), H4); apply H3; erewrite H0; eauto.
  eapply eequiva_weaken with (5:=X0); auto; simplMR; trivial.
 Qed.

 Lemma eequiva_assign_l : forall Q E1 E2 t1 (x1:Var.var t1) e1,
  eequiva (upd1 Q x1 e1) E1 [x1 <- e1] E2 nil Q (fun _ => R1) (fzero _).
 Proof.
  unfold eequiva; intros.
  exists (Munit (m1{!x1<--E.eval_expr e1 m1!}, m2)); intros.
  rewrite deno_assign; rewrite deno_nil. 
  apply le_lift_asym_Munit; trivial.
 Qed.

 Lemma eequiva_assign_r : forall Q E1 E2 t2 (x2:Var.var t2) e2,
  eequiva (upd2 Q x2 e2) E1 nil E2 [x2 <- e2] Q (fun _ => R1) (fzero _).
 Proof.
  unfold eequiva; intros.
  exists (Munit (m1, m2{!x2<--E.eval_expr e2 m2!})); intros.
  rewrite deno_assign; rewrite deno_nil.
  apply le_lift_asym_Munit; trivial.
 Qed.
 
 Lemma eequiva_assign : forall Q E1 E2 t1 (x1:Var.var t1) t2 (x2:Var.var t2) e1 e2, 
  eequiva (upd_para Q x1 e1 x2 e2) E1 [x1 <- e1] E2 [x2 <- e2] Q 
  (fun _ => R1) (fzero _).
 Proof.
  unfold eequiva; intros.
  exists (Munit (m1{!x1<-- E.eval_expr e1 m1!}, m2{!x2<--E.eval_expr e2 m2!})).
  intros; repeat rewrite deno_assign.
  apply le_lift_asym_Munit; trivial.
 Qed.

 Lemma eequiva_random_lift : forall (P Q:mem_rel) E1 E2 t1 t2 (x1:Var.var t1) 
  (x2:Var.var t2) (d1:DE.support t1) (d2:DE.support t2) lam ep,
  (forall k (m1 m2:Mem.t k), sig (fun d => P _ m1 m2 -> 
   le_lift_asym (fun v1 v2 => Q _ (m1 {!x1 <-- v1!}) (m2 {!x2 <-- v2!})) 
   d (DE.eval_support d1 m1)
   (DE.eval_support d2 m2) (lam k) (ep k))) ->
  eequiva P E1 [x1 <$- d1] E2 [x2 <$- d2] Q lam ep.
 Proof.
  unfold eequiva; intros.
  destruct (X _ m1 m2) as (d,Hd); clear X.
  exists (Mlet d 
   (fun v12 => Munit ((m1 {!x1 <-- fst v12!}),(m2 {!x2 <-- snd v12!})))).
  intros Hm; repeat rewrite deno_random.
  apply le_lift_asym_weaken with (@Q k) (lam k * R1)%R (ep k + (lam k) ** 0).
  trivial.
  rewrite Rmult_1_r; auto.
  rewrite multRU_0_r; auto.  
  refine (le_lift_asym_Mlet _ _ _ _ 
   (cover_eq_prod _ _ (carT_cover _ _) (carT_cover _ _)) _ (Rle_refl _) (Hd Hm) _).
  refine (le_lift_asym_discr_witness _ _  (carT_cover _ _) (carT_cover _ _) 
   (DE.discrete_support _ _) (DE.discrete_support _ _) (Hd Hm)).
  intros; apply le_lift_asym_Munit; trivial.
 Qed.

  Lemma eequiva_random_discr: forall (P:mem_rel) E1 E2 t (x1:Var.var t) 
   (x2:Var.var t) (d1:DE.support t) (d2:DE.support t) lam (ep:nat -o> U) 
   (F: forall k, T.interp k t -> U),
   (forall k, 1 <= lam k)%R ->
   (forall k (m1 m2:Mem.t k), P k m1 m2 ->
     le_dist_asym (DE.eval_support d1 m1) (DE.eval_support d2 m2) (lam k) (ep k)) ->
   eequiva P E1 [x1 <$- d1] E2 [x2 <$- d2] (EP_eq_expr x1 x2) lam ep.
  Proof.
   intros.
   apply eequiva_random_lift. 
   intros k m1 m2.
   set (p := parity_split (D_points (DE.discrete_support d1 m1))
    (D_points (DE.discrete_support d2 m2))).
   set (d' := Mlet (dmin (carT k t) (carT_cover k t) p
    (DE.eval_support d1 m1) (DE.eval_support d2 m2)) (fun a => Munit (a, a))).
   exists d'; intros Hm.
   eapply le_lift_asym_weaken; 
    [ | | | apply (@le_lift_asym_eq_intro _ _ (carT_cover k t) _ _
     (DE.discrete_support d1 m1) (DE.discrete_support d2 m2) 
     (lam k) (ep k) (H k)) ]; auto.
   intros; unfold EP_eq_expr; simpl; subst; rewrite 2 Mem.get_upd_same; trivial.
  Qed.

 Import Rpow_def.

 Lemma eequiva_nwhile_cte : forall (P:mem_rel) E1 
  (e1:E.expr T.Bool) c1 E2 (e2:E.expr T.Bool) c2 lam ep n,
  (forall k, 1 <= lam k)%R ->
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
  eequiva (P /-\ EP1 e1 /-\ EP2 e2) E1 c1 E2 c2 P lam ep -> 
  eequiva P E1 (unroll_while e1 c1 n) E2 (unroll_while e2 c2 n) P
  (fun k => pow (lam k) n) (fun k => sum_powR (lam k) (ep k) n).
 Proof.
  intros I E1 e1 c1 E2 e2 c2 lam ep n Hlam I_e Hc.
  induction n; simpl.
  (* base case *)
  refine (eequiva_cond _ _ _ I_e).
  intros _; auto with real.
  eapply eequiva_weaken; 
   [  rewrite proj1_MR | | | | apply eequiva_nil with (P:=I) ]; auto.
  eapply eequiva_weaken; 
   [  rewrite proj1_MR | | | | apply eequiva_nil with (P:=I) ]; auto.

  (* inductive case *)
  refine (eequiva_cond _ _ _ I_e).
 
  intro; rewrite <-(Rmult_1_l 1%R); apply Rmult_le_compat; trivial; try fourier.
  apply pow_R1_Rle; trivial.

  apply eequiva_seq with I; trivial. 
  intros; apply pow_R1_Rle; trivial.

  eapply eequiva_weaken with I I (fun _ => R1) (fzero _);
   [  rewrite proj1_MR | | | | ]; auto.

  intro; rewrite <-(Rmult_1_l 1%R); apply Rmult_le_compat; trivial; try fourier.
  apply pow_R1_Rle; trivial.

  apply eequiva_nil.
 Qed.


 Section nWHILE.

  Variables c1 c2 : cmd.

  Variables e1 e2 : env.

  Variable I : mem_rel.

  Variables b1 b2 : E.expr T.Bool.

  Variable k : nat.

  Variable ep : U.
 
  Variable lam : R.

  Hypothesis H_lam : (1 <= lam)%R.
 
  Variable q : nat.

  Hypothesis Hc: forall m1 m2 : Mem.t k, 
   sig (fun d =>
    (I /-\ EP1 b1 /-\ EP2 b2) _ m1 m2 ->
    le_lift_asym 
    ((I /-\ EP_eq_expr b1 b2) k) d 
    (([[ c1 ]]) e1 m1) (([[ c2 ]]) e2 m2) 
    lam ep).

  Lemma nwhile_le_lift_asym : forall m1 m2 : Mem.t k,
   sig (fun d' => (I /-\ EP_eq_expr b1 b2) _ m1 m2 ->
    le_lift_asym ((I /-\ ~- EP1 b1 /-\ ~- EP2 b2) k) d' 
    (drestr ([[ unroll_while b1 c1 q ]] e1 m1) (negP (EP k b1))) 
    (drestr ([[ unroll_while b2 c2 q ]] e2 m2) (negP (EP k b2)))
    (pow lam q) (sum_powR lam ep q)).
  Proof.
   unfold EP_eq_expr; induction q; intros m1 m2.
   (* base case *)
   case_eq (E.eval_expr b1 m1); intro Heq.
   (* case [b1] *)
   exists (distr0 _); intros (H1m, H2m).
   rewrite (eq_distr_intro _ (Munit m1) (unroll_while_0_elim e1 b1 c1 m1)),
    (eq_distr_intro _ (Munit m2) (unroll_while_0_elim e2 b2 c2 m2)).
   unfold drestr, negP, negb, EP; rewrite 2 Mlet_unit, <-H2m, Heq.
   eapply le_lift_asym_eq_compat; [ apply Oeq_refl |  | | | | apply le_lift_asym_prod ];
    auto.
   (* case [~b1] *)
   exists (Munit (m1, m2)); intros (H1m, H2m).
   rewrite (eq_distr_intro _ (Munit m1) (unroll_while_0_elim e1 b1 c1 m1)),
    (eq_distr_intro _ (Munit m2) (unroll_while_0_elim e2 b2 c2 m2)).
   unfold drestr, negP, negb, EP; rewrite 2 Mlet_unit, <-H2m, Heq.
   apply le_lift_asym_Munit.
   trivial.
   unfold EP1, EP2, notR; repeat split; [ trivial | | rewrite <-H2m ];
    apply (proj2 (not_true_iff_false _) Heq).
   (* inductive case *)
   case_eq (E.eval_expr b1 m1); intro Heq.
   (* case [b1] *)
   destruct (Hc m1 m2) as (d',Hd'); clear Hc.
   exists (Mlet d' 
    (fun mm => proj1_sig (IHn (fst mm) (snd mm)))); intros (H1m,H2m).
   simpl; rewrite deno_cond, deno_cond, <-H2m, Heq.
   unfold drestr; repeat rewrite deno_app, (Mcomp _ _ _).
   apply le_lift_asym_Mlet with 
    ((I /-\ (EP_eq_expr b1 b2)) k)
    (fun ab ab' => mem_eqU (fst ab) (fst ab') * mem_eqU (snd ab) (snd ab')).
   apply (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)); auto.
   refine (le_lift_asym_discr_witness _ _ (@mem_eqU_spec k) (@mem_eqU_spec k) 
    (sem_discr _ _ _) (sem_discr _ _ _) (Hd' _)); 
   repeat split; [ trivial | | unfold EP2; rewrite <-H2m ]; apply Heq.
   apply pow_R1_Rle; trivial.
   apply Hd'. 
   repeat split; [ trivial | | unfold EP2; rewrite <-H2m ]; apply Heq.
   intros m1' m2' Hm'; unfold fst, snd.
   destruct (IHn m1' m2') as (dn,Hdn); auto.
   (* case [~b1] *)
   exists (Munit (m1,m2)); intros (H1m, H2m).
   simpl; rewrite deno_cond, deno_cond, <-H2m, Heq.
   unfold drestr, negP, negb, EP.
   rewrite deno_nil, deno_nil, Mlet_unit, Mlet_unit, <-H2m, Heq.
   eapply le_lift_asym_weaken; [  intros ? ? H'; apply H' | | | 
    apply le_lift_asym_Munit ]; trivial.
   rewrite <-(Rmult_1_l 1%R); apply Rmult_le_compat; try fourier.
   apply pow_R1_Rle; trivial.
   unfold EP1, EP2, notR; repeat split; [ trivial | | rewrite <-H2m ];
    apply (proj2 (not_true_iff_false _) Heq).
  Qed.
 
 End nWHILE.


 Lemma eequiva_while : forall (P P':mem_rel) E1 (e1:E.expr T.Bool) c1 E2 
  (e2:E.expr T.Bool) c2 lam ep q,
  implMR P' P ->
  (forall k, 1 <= lam k)%R ->
  (forall k (m1 m2:Mem.t k),  (P' /-\ EP_eq_expr e1 e2) _ m1 m2 -> 
   [[ [while e1 do c1] ]] E1 m1 == 
   drestr ([[ unroll_while e1 c1 (q k) ]] E1 m1) (negP (@EP k e1)) /\
   [[ [while e2 do c2] ]] E2 m2 == 
   drestr ([[ unroll_while e2 c2 (q k) ]] E2 m2) (negP (@EP k e2))) ->
  eequiva (P /-\ EP1 e1 /-\ EP2 e2) E1 c1 E2 c2 (P /-\ EP_eq_expr e1 e2) lam ep -> 
  eequiva (P' /-\ EP_eq_expr e1 e2) 
  E1 [while e1 do c1] 
  E2 [while e2 do c2] 
  (P /-\ ~-EP1 e1 /-\ ~-EP2 e2) 
  (fun k => pow (lam k) (q k))
  (fun k => sum_powR (lam k) (ep k) (q k)).
 Proof.
  unfold eequiva; intros.  
  destruct (nwhile_le_lift_asym (H0 k) (q k) (X k) m1 m2) as (d,Hd).
  exists d; intro Hm.
  apply le_lift_asym_eq_compat with 
   (6:=Hd (andR_impl_morph H (implMR_refl (EP_eq_expr e1 e2)) Hm)); trivial.
  symmetry; apply (proj1 (H1 _ _ _ Hm)).
  symmetry; apply (proj2 (H1 _ _ _ Hm)).
 Qed.


 Lemma assert_assign_comm_asym : forall E1 E2 t 
  (x1 x2:Var.var t) e1 e2 b1 b2 (P Q:mem_rel),
  (forall k (m1 m2: Mem.t k), 
   P _ m1 m2 ->
   @E.eval_expr k T.Bool b1 (m1 {!x1 <-- E.eval_expr e1 m1!}) = 
   E.eval_expr b2 m2 /\
   Q _ (m1 {!x1 <-- E.eval_expr e1 m1!}) (m2 {!x2 <-- E.eval_expr e2 m2!})) ->
  eequiva P 
  E1 [ x1 <- e1; Assert b1] 
  E2 [ Assert b2; x2 <- e2 ] 
  Q (fun _ => R1) (fzero _).
 Proof.
  intros; intros k m1 m2.
  exists  (if @E.eval_expr k T.Bool b1 (m1 {!x1 <-- E.eval_expr e1 m1!}) then
   Munit (m1 {!x1 <-- E.eval_expr e1 m1!},m2 {!x2 <-- E.eval_expr e2 m2!}) 
   else distr0 _); intro Hm.
  rewrite (deno_cons _ (_ <- _) [Assert _]),
   (deno_cons _ (Assert _) [_ <- _]), deno_assign, 
   deno_assert, Mlet_unit, deno_assert. 
  repeat setoid_rewrite (proj1 (H _ _ _ Hm)).
  case (E.eval_expr b2 m2).
  rewrite Mlet_unit, deno_assign.
  apply (le_lift_asym_Munit _ _ _ (Rle_refl _) (proj2 (H _ _ _ Hm))).
  rewrite Mlet_distr0_abs.
  apply (le_lift_asym_distr0 _ _ (Rle_refl _)).
 Qed.
 
 Lemma eequiva_trans_l : forall (P1 P2 Q1 Q2 Q3:mem_rel) 
  E1 c1 E2 c2 E3 c3 ep1 ep2 lam1 lam2 ep lam,
  (forall k, 1 <= lam1 k)%R ->
  (forall k, 1 <= lam2 k)%R ->
  (forall k, lam1 k * lam2 k <= lam k)%R ->
  (forall k, ep1 k + lam1 k ** ep2 k <= ep k) ->
  decMR P2 ->
  refl_supMR2 P2 P1 ->
  (forall k x y z, Q1 k x y -> Q2 k y z -> Q3 k x z) -> 
  eequiva P1 E1 c1 E2 c2 Q1 lam1 ep1 -> 
  eequiva P2 E2 c2 E3 c3 Q2 lam2 ep2 ->
  eequiva P2 E1 c1 E3 c3 Q3 lam ep.
 Proof.
  unfold eequiva; intros. 
  destruct (X0 _ m1 m1) as (d, Hd); destruct (X1 _ m1 m2) as (d',Hd').
  destruct (X _ m1 m2).
  exists (@dd'_asym _ _ _ (@mem_eqU k) 
   (Q1 k) (Q2 k) d d' 
   (ep1 k) (ep2 k) (lam1 k) (lam2 k) 
   (@deno k c1 E1 m1) (@deno k c2 E2 m1) (@deno k c3 E3 m2) 
   (Hd (H3 k m1 m2 p))
   (Hd' p)).
  intros _.
  eapply le_lift_asym_weaken; [ | | | 
  apply (le_lift_asym_trans_discr _ _ _ (@mem_eqU_spec k)
   (@mem_eqU_spec k) (@mem_eqU_spec k) _ (@H4 k) (Hd (H3 _ _ _ p))
   (Hd' p) (sem_discr _ _ _) (sem_discr _ _ _)) ]; auto.
  exists (distr0 _).
  intro; contradiction.
 Qed.

 Section RANDOM_ASSERT_ASYM.

  Variable E1 E2 : env.

  Variable t : T.type.

  Variables d1 d2 : DE.support t.

  Variable P : mem_rel.

  Variable F : forall k, T.interp k t -> U.

  Variables e1 e2 : E.expr T.Bool.
 
  Variables x1 x2 : Var.var t.

  Variable lam : nat -> R.

  Variable ep : nat -o> U.

  Let d1i k (m:Mem.t k) := DE.eval_support d1 m. 
 
  Let d2i k (m:Mem.t k) := DE.eval_support d2 m. 
 
  Let d1i' k (m:Mem.t k) := 
   drestr (DE.eval_support d1 m) (fun v => E.eval_expr e1 (m{!x1 <-- v!})). 
  
  Let d2i' k (m:Mem.t k) :=
   drestr (DE.eval_support d2 m) (fun v => E.eval_expr e2 (m{!x2 <-- v!})). 

  Lemma d1'_discr_asym: forall k (m:Mem.t k), is_Discrete (d1i' m).
  Proof.
   intros; apply (is_Discrete_Mlet _ (DE.discrete_support _ _)).
   intros a; case (E.eval_expr e1 (m {!x1 <-- a!}));
    [ apply is_Discrete_Munit | apply (is_Discrete_distr0 (T.default k t)) ].
  Defined.

  Lemma d2'_discr_asym: forall k (m:Mem.t k), is_Discrete (d2i' m).
  Proof.
   intros; apply (is_Discrete_Mlet _ (DE.discrete_support _ _)).
   intros a; case (E.eval_expr e2 (m {!x2 <-- a!}));
    [ apply is_Discrete_Munit | apply (is_Discrete_distr0 (T.default k t)) ].
  Defined.

  Hypothesis foo: forall k (m1 m2:Mem.t k), 
   P m1 m2 ->  
   le_dist_asym (d1i' m1) (d2i' m2) (lam k) (ep k).

  Let p k (m1 m2:Mem.t k) := 
   parity_split (D_points (d1'_discr_asym m1)) (D_points (d2'_discr_asym m2)).

  Hypothesis Hlam : forall k, (1 <= lam k)%R.

  Lemma eequiva_random_assert:
   eequiva P 
   E1 [x1 <$- d1; Assert e1] 
   E2 [x2 <$- d2; Assert e2] 
   (EP_eq_expr x1 x2) lam ep.
  Proof.
   intros k m1 m2.
   set (d':=Mlet 
    (dmin (carT k t) (carT_cover k t) (p m1 m2) (d1i' m1)  (d2i' m2)) 
    (fun a => Munit (a, a))).
   assert (Hd':is_Discrete d') by 
    refine (is_Discrete_Mlet _ (is_discrete_Discrete _) (fun a => is_Discrete_Munit (a,a))).
   set (d'':=Mlet d' (fun vs => Munit (m1{!x1 <-- fst vs!}, m2{!x2 <-- snd vs!}))).
   exists d''; intros Hm.
   eapply le_lift_asym_eq_compat with 
    (d1:= Mlet  (d1i' m1) (fun v => Munit (m1 {!x1 <-- v!})))
    (d2:= Mlet  (d2i' m2) (fun v => Munit (m2 {!x2 <-- v!}))) 
    (lam:= (lam k * R1)%R)
    (ep := ep k + (lam k) ** 0); trivial.
   unfold d1i', drestr;
    rewrite (deno_cons _ (_ <$- _) [Assert _]), deno_random, 2 Mcomp;
    apply (Mlet_eq_compat (Oeq_refl _)); refine (ford_eq_intro _); intro v;
    rewrite Mlet_unit, deno_assert;
    case (E.eval_expr e1 (m1 {!x1 <-- v!})); 
     [ rewrite Mlet_unit; trivial | apply Mlet_distr0_abs ].
   unfold d2i', drestr;
    rewrite (deno_cons _ (_ <$- _) [Assert _]), deno_random, 2 Mcomp;
    apply (Mlet_eq_compat (Oeq_refl _)); refine (ford_eq_intro _); intro v;
    rewrite Mlet_unit, deno_assert;
    case (E.eval_expr e2 (m2 {!x2 <-- v!})); 
     [ rewrite Mlet_unit; trivial | apply Mlet_distr0_abs ].
   rewrite Rmult_1_r; auto.
   repeat multRU_simpl; repeat Usimpl; auto.
   refine (le_lift_asym_Mlet _ _ _ _
    (cover_eq_prod _ _ (carT_cover _ _) (carT_cover _ _)) Hd' (Rle_refl _) _ _).
   eapply le_lift_asym_weaken with (P:=@eq (T.interp k t)); 
    [ | | | apply (@le_lift_asym_eq_intro _ _ 
     (carT_cover k t) _ _ 
     (d1'_discr_asym m1) (d2'_discr_asym m2) (lam k) 
     (ep k) (Hlam k)) ]; auto.
   intros v1 v2 Hv; subst; simpl.
   apply le_lift_asym_Munit; trivial.
   unfold EP_eq_expr; simpl; rewrite 2 Mem.get_upd_same; trivial.
  Qed.
 
  Lemma eequiva_random_assert_strong: 
   (forall k (m1 m2:Mem.t k) v, 
    P m1 m2 -> 
    E.eval_expr e1 (m1{!x1 <-- v!}) = E.eval_expr e2 (m2{!x2 <-- v!})) ->
   eequiva P 
   E1 [x1 <$- d1; Assert e1] 
   E2 [x2 <$- d2; Assert e2] 
   (EP_eq_expr x1 x2 /-\ EP1 e1 /-\ EP2 e2) lam ep.
  Proof.
   intros Hequiv k m1 m2.
   set (d':=Mlet (dmin (carT k t) (carT_cover k t) (p m1 m2) (d1i' m1) (d2i' m2)) 
    (fun a => Munit (a, a))).
   assert (Hd':is_Discrete d') by 
    refine (is_Discrete_Mlet _ 
     (is_discrete_Discrete _) (fun a => is_Discrete_Munit (a,a))).
   set (d'':= Mlet d' 
    (fun vs => 
     if (E.eval_expr e1 (m1{!x1 <-- fst vs!}) && 
         E.eval_expr e2 (m2{!x2 <-- snd vs!})) then
     Munit (m1 {!x1 <-- fst vs!},m2 {!x2 <-- snd vs!}) else distr0 _)).
   exists d''; intros Hm.
   eapply le_lift_asym_eq_compat with 
    (d1:=Mlet (d1i' m1) 
    (fun v => 
     if E.eval_expr e1 (m1{!x1 <-- v!}) then Munit (m1{!x1 <-- v!}) else distr0 _))
    (d2:= Mlet  (d2i' m2) 
    (fun v => 
     if E.eval_expr e2 (m2{!x2 <-- v!}) then Munit (m2{!x2 <-- v!}) else distr0 _))
    (lam:=(lam k * 1)%R)
    (ep :=ep k + (lam k) ** 0); trivial.
   unfold d1i', drestr;
   rewrite (deno_cons _ (_ <$- _) [Assert _]), deno_random, 2 Mcomp;
   apply (Mlet_eq_compat (Oeq_refl _)); refine (ford_eq_intro _); 
   intro v; rewrite Mlet_unit; rewrite deno_assert.
   case_eq (E.eval_expr e1 (m1 {!x1 <-- v!})); intro Heq;
    [rewrite Mlet_unit, Heq | apply Mlet_distr0_abs; rewrite Heq]; trivial.
   unfold d2i', drestr;
   rewrite (deno_cons _ (_ <$- _) [Assert _]), deno_random, 2 Mcomp;
    apply (Mlet_eq_compat (Oeq_refl _)); refine (ford_eq_intro _); intro v;
    rewrite Mlet_unit, deno_assert;
    case_eq (E.eval_expr e2 (m2 {!x2 <-- v!})); intro Heq;
     [ rewrite Mlet_unit; rewrite Heq; trivial | apply Mlet_distr0_abs ].
   rewrite Rmult_1_r; auto.
   repeat multRU_simpl; repeat Usimpl; auto.

   refine (le_lift_asym_Mlet _ _ _ _
    (cover_eq_prod _ _ (carT_cover _ _) (carT_cover _ _)) Hd' (Rle_refl _) _ _).
   eapply le_lift_asym_weaken with (P:=@eq (T.interp k t)); 
    [ | | | apply (@le_lift_asym_eq_intro _ _ (carT_cover k t) _ _
     (d1'_discr_asym m1) (d2'_discr_asym m2) (lam k) (ep k) (Hlam k)) ]; auto.
   intros v1 v2 Hv; subst; simpl.
   case_eq (E.eval_expr e1 (m1 {!x1 <-- v2!})); intros H1;
    case_eq (E.eval_expr e2 (m2 {!x2 <-- v2!})); intros H2; simpl.
   apply le_lift_asym_Munit; trivial.
   unfold EP_eq_expr; simpl; repeat split. 
   rewrite 2 Mem.get_upd_same; trivial.
   unfold EP1; trivial.
   unfold EP2; trivial.
   rewrite Hequiv with (m2:=m2) in H1.
   rewrite H2 in H1; discriminate H1.
   rewrite Hequiv with (m2:=m2) in H1.
   rewrite H2 in H1; discriminate H1.
   trivial.
   rewrite Hequiv with (m2:=m2) in H1.
   rewrite H2 in H1; discriminate H1.
   rewrite Hequiv with (m2:=m2) in H1.
   rewrite H2 in H1; discriminate H1.
   trivial.
   apply le_lift_asym_distr0.
   trivial.
  Qed.

 End RANDOM_ASSERT_ASYM.


  Lemma eequiva_assert_app : forall E1 E2 c1 c1' c2 c2' e1 e2 P Q lam1 lam2,
  (forall k, 1 <= lam1 k)%R ->
  (forall k, 1 <= lam2 k)%R ->
  decMR P ->
  eequiva P 
  E1 (c1 ++ [Assert e1] ++ c1') 
  E2 (c2 ++ [Assert e2] ++ c2')
  Q lam1 (fun k => 0) -> 
  eequiva P 
  E1 (c1 ++ [Assert !e1] ++ c1') 
  E2 (c2 ++ [Assert !e2] ++ c2')
  Q lam2 (fun k => 0) -> 
  eequiva P 
  E1 (c1 ++ c1')
  E2 (c2 ++ c2')
  Q 
  (fun k => Rmax (lam1 k) (lam2 k)) (fun k => 0).
 Proof.
  unfold eequiva; intros E1 E2 c1 c1' c2 c2' e1 e2 P Q lam1 lam2 Hlam1 Hlam2 HP
   H1 H2 k m1 m2.
  destruct (H1 k m1 m2) as [d1 Hd1]; clear H1.
  destruct (H2 k m1 m2) as [d2 Hd2]; clear H2.
  case (HP k m1 m2); clear HP; intro HP; [ | exists (distr0 _); tauto].
  
  assert (W:mu d1 (fone _) <= [1-] mu d2 (fone _)).
  destruct (Hd1 HP); clear Hd1.
  destruct (Hd2 HP); clear Hd2.

  transitivity (mu (Mfst d1) (fone _)).
  simpl; refine (mu_monotonic _ _ _ _); trivial.
  transitivity ([1-] mu (Mfst d2) (fone _));
   [ | simpl; apply Uinv_le_compat; refine (mu_monotonic _ _ _ _); trivial].
  rewrite le_p1_asym.
  rewrite deno_app_elim.
  eapply Ole_trans; [ | apply Uinv_le_compat; apply le_p1_asym0].
  rewrite deno_app_elim.
  eapply Ole_trans; [ | apply mu_stable_inv ].
  refine (mu_monotonic _ _ _ _); intro.
  unfold finv.
  rewrite deno_app_elim, deno_app_elim.
  rewrite deno_assert_elim, deno_assert_elim, eval_negb.
  case (E.eval_expr e1 x); unfold finv, fone; simpl; auto.
  
  exists (Mplus d1 d2 W); intro.
  constructor; trivial.
  apply Rmax_case; trivial.

  intros.
  simpl.
  destruct (Hd1 HP); clear Hd1.
  destruct (Hd2 HP); clear Hd2.
  rewrite <-multRU_distr_plus_l; [ | trivial].
  generalize (le_d_asym  f); clear le_d_asym;  intros.
  generalize (le_d_asym0 f); clear le_d_asym0; intros.
  
  rewrite (deno_app_elim E1 c1 c1' m1).
  rewrite mu_restr_split with (P:=EP k e1) (d:=[[c1]] E1 m1).
  eapply Ole_trans.
  apply Uplus_minus_perm_assoc.
  unfold restr.
  rewrite <-(Uplus_zero_left 0); apply Uplus_le_compat.
  rewrite deno_app_elim in H0.
  simpl in H0. 
  rewrite <-H0.
  apply Uminus_le_compat.
  apply mu_monotonic; intro m'.
  rewrite (deno_cons_elim E1 (Assert e1) c1' m'), Mlet_simpl.
  rewrite deno_assert_elim; trivial.
  apply multRU_le_compat.
  fourier.
  apply Rmax_l.
  auto.

  rewrite deno_app_elim in H1.
  simpl in H1. 
  rewrite <-H1.
  apply Uminus_le_compat.
  apply mu_monotonic; intro m'.
  rewrite (deno_cons_elim E1 (Assert !e1) c1' m'), Mlet_simpl.
  rewrite deno_assert_elim; trivial.
  apply multRU_le_compat.
  fourier.
  apply Rmax_r.
  trivial.

  apply Rmax_case; trivial.

  (* Finally *)
  intros ? ?.
  rewrite Mplus_elim.
  rewrite <-Uplus_zero_left; apply Uplus_eq_compat.
  destruct (Hd1 HP); apply le_r_asym; trivial.
  destruct (Hd2 HP); apply le_r_asym; trivial.

  intros.
  rewrite deno_app_elim.
  rewrite mu_restr_split with (P:=EP k e1) (d:=[[c1]] E1 m1).
  unfold restr, Mfst; rewrite Mlet_simpl, Mplus_elim.
  apply Uplus_le_compat.
  destruct (Hd1 HP).
  unfold Mfst in le_p1_asym.
  simpl in le_p1_asym |- *.
  rewrite le_p1_asym.
  rewrite (deno_app_elim E1 c1 ((Assert e1) :: c1') m1).
  apply mu_monotonic; intro m'.
  rewrite deno_cons_elim, Mlet_simpl, deno_assert_elim; trivial.
  
  destruct (Hd2 HP).
  unfold Mfst in le_p1_asym.
  simpl in le_p1_asym |- *.
  rewrite le_p1_asym.
  rewrite (deno_app_elim E1 c1 ((Assert !e1) :: c1') m1).
  apply mu_monotonic; intro m'.
  rewrite deno_cons_elim, Mlet_simpl, deno_assert_elim; trivial.

  intros.
  rewrite deno_app_elim.
  rewrite mu_restr_split with (P:=EP k e2) (d:=[[c2]] E2 m2).
  unfold restr, Msnd; rewrite Mlet_simpl, Mplus_elim.
  apply Uplus_le_compat.
  destruct (Hd1 HP).
  unfold Msnd in le_p2_asym.
  simpl in le_p2_asym |- *.
  rewrite le_p2_asym.
  rewrite (deno_app_elim E2 c2 ((Assert e2) :: c2') m2).
  apply mu_monotonic; intro m'.
  rewrite deno_cons_elim, Mlet_simpl, deno_assert_elim; trivial.
  
  destruct (Hd2 HP).
  unfold Msnd in le_p2_asym.
  simpl in le_p2_asym |- *.
  rewrite le_p2_asym.
  rewrite (deno_app_elim E2 c2 ((Assert !e2) :: c2') m2).
  apply mu_monotonic; intro m'.
  rewrite deno_cons_elim, Mlet_simpl, deno_assert_elim; trivial.
 Qed.
 
 Lemma eequiva_assert_join : forall E1 E2 e1 e2 c1 c2 P Q lam1 lam2,
  (forall k, 1 <= lam1 k)%R ->
  (forall k, 1 <= lam2 k)%R ->
  eequiva P E1 (c1 ++ [Assert  e1]) E2 (c2 ++ [Assert  e2]) Q lam1 (fun k => 0) ->
  eequiva P E1 (c1 ++ [Assert !e1]) E2 (c2 ++ [Assert !e2]) Q lam2 (fun k => 0) ->
  decMR P ->
  eequiva P E1 c1 E2 c2 Q (fun k => Rmax (lam1 k) (lam2 k)) (fun k => 0).
 Proof.
  unfold eequiva.
  intros E1 E2 e1 e2 c1 c2 P Q lam1 lam2 Hlam1 Hlam2 H1 H2 HP k m1 m2.
  destruct (H1 k m1 m2) as [d1 Hd1]; clear H1. 
  destruct (H2 k m1 m2) as [d2 Hd2]; clear H2.
  destruct (HP _ m1 m2) as [Hm | Hm].

  assert (W:mu d1 (fone _) <= [1-] mu d2 (fone _)).
  destruct (Hd1 Hm); clear Hd1.
  destruct (Hd2 Hm); clear Hd2.

  transitivity (mu (Mfst d1) (fone _)).
  simpl; refine (mu_monotonic _ _ _ _); trivial.
  transitivity ([1-] mu (Mfst d2) (fone _));
   [ | simpl; apply Uinv_le_compat; refine (mu_monotonic _ _ _ _); trivial].
  rewrite le_p1_asym.
  rewrite deno_app_elim.
  eapply Ole_trans; [ | apply Uinv_le_compat; apply le_p1_asym0].
  rewrite deno_app_elim.
  eapply Ole_trans; [ | apply mu_stable_inv ].
  refine (mu_monotonic _ _ _ _); intro.
  unfold finv.
  rewrite deno_assert_elim, deno_assert_elim, eval_negb.
  case (E.eval_expr e1 x); unfold finv, fone; simpl; auto.
   
  exists (Mplus d1 d2 W).
  apply (Rmax_case_strong (lam1 k) (lam2 k)); intros Hle H.

  (* lam2 <= lam1 *)
  destruct (Hd1 H); clear Hd1.
  destruct (Hd2 H); clear Hd2.  
  constructor; intros; trivial.
  
  simpl.
  rewrite <-multRU_distr_plus_l; [ | trivial].
  generalize (le_d_asym  f); clear le_d_asym;  intros.
  generalize (le_d_asym0 f); clear le_d_asym0; intros.
  generalize (Uminus_zero_le (Ule_zero_eq _ H0)); clear H0; intro H1'.   
  generalize (Uminus_zero_le (Ule_zero_eq _ H1)); clear H1; intro H2'.
  apply Uminus_le_zero.
  rewrite (deno_app_assert_elim e1 E1 c1 m1).
  rewrite H1', H2'. 
  apply Uplus_le_compat; trivial.
  apply multRU_le_compat; trivial.
  fourier. 

  intros f Hf; simpl.
  rewrite <-Uplus_zero_left; apply Uplus_eq_compat; auto.

  rewrite (deno_app_assert_elim e1 E1 c1 m1).
  simpl in le_p1_asym0, le_p1_asym |- *; rewrite  le_p1_asym0, le_p1_asym; trivial.

  rewrite (deno_app_assert_elim e2 E2 c2 m2); trivial.
  simpl in le_p2_asym, le_p2_asym0 |- *; rewrite le_p2_asym, le_p2_asym0; trivial.

  (* lam1 <= lam2 *)
  destruct (Hd1 H); clear Hd1.
  destruct (Hd2 H); clear Hd2.  
  constructor; intros; trivial.

  simpl.
  rewrite <-multRU_distr_plus_l; [ | trivial].
  generalize (le_d_asym  f); clear le_d_asym;  intros.
  generalize (le_d_asym0 f); clear le_d_asym0; intros.
  generalize (Uminus_zero_le (Ule_zero_eq _ H0)); clear H0; intro H1'.   
  generalize (Uminus_zero_le (Ule_zero_eq _ H1)); clear H1; intro H2'.
  apply Uminus_le_zero.
  rewrite (deno_app_assert_elim e1 E1 c1 m1).
  rewrite H1', H2'. 
  apply Uplus_le_compat; trivial.
  apply multRU_le_compat; trivial.
  fourier. 

  intros f Hf; simpl.
  rewrite <-Uplus_zero_left; apply Uplus_eq_compat; auto.

  rewrite (deno_app_assert_elim e1 E1 c1 m1).
  simpl in le_p1_asym0, le_p1_asym |- *; rewrite le_p1_asym0, le_p1_asym; trivial.

  rewrite (deno_app_assert_elim e2 E2 c2 m2); trivial.
  simpl in le_p2_asym, le_p2_asym0 |- *; rewrite le_p2_asym, le_p2_asym0; trivial.

  exists d1.
  intro; contradiction.
 Qed.


Section SPLIT_WHILE_ASYM.

  Variables E1 E2 : env.

  Variables c1 c2 : cmd.
  
  Variables b1 b2 P1 P2 : E.expr T.Bool.
 
  Variables I : mem_rel.

  Variable i : Var.var T.Nat.

  Variable HI1 : implMR I (EP_eq_expr b1 b2).

  Variable HI2 : implMR I (EP_eq_expr P1 P2).
 
  Variable k : nat.

  Variable lam1 : nat -> R.

  Variable lam2 : R.

  Hypothesis Hlam1 : forall k, (1 <= lam1 k)%R. 
 
  Hypothesis Hlam2 : (1 <= lam2)%R. 

  Hypothesis H1 : forall j:nat, 
   eequiva 
   (I /-\ EP1 b1 /-\ EP1 (i =?= j) /-\ EP1 (!P1) )
   E1 (c1 ++ [ Assert !P1 ])
   E2 (c2 ++ [ Assert !P2 ]) 
   (I /-\ EP1 (i =?= S j) /-\ EP1 (!P1)) 
   (fun k => lam1 j) (fun k => 0).

  Hypothesis H2 : forall j:nat,
   eequiva 
   (I /-\ EP1 b1 /-\ EP1 (i =?= j) /-\ EP1 (!P1))
   E1 (c1 ++ [ Assert P1 ])
   E2 (c2 ++ [ Assert P2 ])
   (I /-\ EP1 (i =?= S j) /-\ EP1 P1) 
   (fun k => lam2) (fun k => 0).

  Hypothesis H3 : forall j:nat,
   equiv 
   ((I /-\ EP1 b1 /-\ EP1 (i =?= j)) /-\ EP1 P1)
   E1 c1 
   E2 c2 
   ((I /-\ EP1 (i =?= S j)) /-\ EP1 P1).

  (** 
     The next two hyptotheses could be replaced by
     Hypothesis H4 : equiv (I /-\ EP1 b1) E1 c1 E2 c2 I
  *)

  Hypothesis range_c1 : forall k (m:Mem.t k),
   EP k P1 m -> range (EP k P1) ([[c1]] E1 m).

  Hypothesis range_c2 : forall k (m:Mem.t k),
   EP k P2 m -> range (EP k P2) ([[c2]] E2 m).

  Lemma split_unroll_first_asym : forall (n a:nat) lam,
   (forall k, 1 <= lam k)%R ->
   (forall k, ProdRR lam1 a n <= lam k)%R ->
   eequiva
   ((I /-\ EP1 (i =?= a)) /-\ ~- EP1 P1)
   E1 (unroll_while b1 (c1 ++ [Assert !P1]) n)
   E2 (unroll_while b2 (c2 ++ [Assert !P2]) n)
   I lam (fun k => 0).  
  Proof.
   induction n; intros a lam Hle Hge.
   apply eequiva_cond; trivial.
   eapply eequiva_weaken; [ | | | | apply eequiva_nil]; trivial.
   unfold implMR, andR; intuition.
   eapply eequiva_weaken; [ | | | | apply eequiva_nil]; trivial.
   unfold implMR, andR; intuition.
   unfold implMR, andR; intuition.
   apply HI1 in H; trivial.

   (* inductive case *)
   simpl.
   eapply eequiva_weaken with 
    (lam':=fun k => _) 
    (ep':=fun k => _);
    [ | | | | apply eequiva_cond]; trivial.
   intros; rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; auto; try fourier.
   apply ProdRR_ge_1; intros; trivial.

   2:eapply eequiva_weaken; [ | | | | apply eequiva_nil]; trivial.
   2:unfold implMR, andR; intuition.
   2:intro; apply ProdRR_ge_1; trivial.
   2:intros ? ? ? [ [? ?] ?]; apply HI1 in H; unfold EP_eq_expr in H; trivial.
   
   eapply eequiva_weaken with 
    (lam':=fun k => (lam1 a * ProdRR lam1 (S a) n)%R) 
    (ep:=fun k => 0) 
    (ep':=fun k => 0 + _ ** 0);
    [ | | | | eapply eequiva_seq with (Q':=(I /-\ EP1 (i =?= S a)) /-\ ~- EP1 P1) ].
   trivial.
   trivial.
   trivial.
   intro; rewrite multRU_0_r; auto.   
   intro; apply ProdRR_ge_1; auto.
   
   eapply eequiva_weaken; [ | | | | apply (H1 a)].
   unfold implMR, andR; intuition.
   apply is_true_negb in H5; trivial.   
   unfold implMR, andR; intuition.
   apply is_true_negb; trivial.
   trivial.
   trivial.

   apply (IHn (S a)).   
   intro; apply ProdRR_ge_1; trivial.
   trivial.
  Qed.

  Lemma split_unroll_last_asym: forall (n a:nat) lam,
   (forall k, 1 <= lam k)%R ->
   eequiva 
   ((I /-\ EP1 (i =?= a)) /-\ EP1 P1)
   E1 (unroll_while b1 c1 n ++ [Assert P1])
   E2 (unroll_while b2 c2 n ++ [Assert P2])
   I lam (fun k => 0).  
  Proof.
   induction n; intros.

   eapply eequiva_weaken; 
    [ | | | | apply eequiva_seq with (Q':=I) (ep:=fun k => 0) (ep':=fun k => 0)
      (lam:=fun k => 1%R) (lam':=fun k => 1%R)].
   trivial.
   trivial.
   intros; rewrite Rmult_1_l; intuition.
   intros n; rewrite multRU_0_r, Uplus_zero_left; trivial.
   trivial.

   apply eequiva_cond; trivial. 
   eapply eequiva_weaken; [ | | | | apply eequiva_nil]; trivial.
   unfold implMR, andR; intuition.   
   eapply eequiva_weaken; [ | | | | apply eequiva_nil]; trivial.
   unfold implMR, andR; intuition.   
   
   intros ? ? ? [ [? _] _]; apply HI1; trivial.
   eapply eequiva_weaken; 
    [ | | | | apply equiv_eequiva; apply equiv_assert with (P:=I)]; trivial.
   unfold implMR, andR; intuition.
   apply HI2; trivial.
   unfold implMR, andR; intuition.

   (* inductive case *)
   simpl unroll_while.
   apply eequiva_case with (P':=EP1 b1); [trivial | | ].

   apply eequiva_eq_compat_l with 
    (c1 ++ unroll_while b1 c1 n ++ [Assert P1]).
   intros ? ? ? ? [ [? ?] ? ].
   symmetry; rewrite deno_app_elim, deno_cond_elim, H5, deno_app_elim; trivial.
   rewrite deno_app_elim.
   apply mu_stable_eq; refine (ford_eq_intro _); intro.
   symmetry; apply deno_app_elim.

   apply eequiva_eq_compat_r with 
    (c2 ++ unroll_while b2 c2 n ++ [Assert P2]).
   intros ? ? ? ? [ [ [? ?] ?] ? ].
   symmetry; rewrite deno_app_elim, deno_cond_elim.
   rewrite <-(HI1 H0), H6, deno_app_elim; trivial.
   rewrite deno_app_elim.
   apply mu_stable_eq; refine (ford_eq_intro _); intro.
   symmetry; apply deno_app_elim.

   eapply eequiva_weaken with (lam':=fun k => _) (ep':=fun k => _);
    [ | | | | eapply eequiva_seq; [ | apply equiv_eequiva, (H3 a) | apply IHn ]  ].
   unfold implMR, andR; intuition.
   trivial.
   intros; simpl.
   rewrite Rmult_1_l; trivial.
   intros ?; rewrite multRU_0_r; Usimpl; trivial.
   trivial.
   trivial.

   apply eequiva_eq_compat_l with [Assert P1].
   intros ? ? ? ? [ [ [? ?] ?] ? ].
   symmetry; rewrite deno_app_elim, deno_cond_elim.
   apply not_is_true_false in H6; rewrite H6, deno_nil_elim; trivial.

   apply eequiva_eq_compat_r with [Assert P2].
   intros ? m1 m2 f [ [ [? ?] ?] ? ].
   symmetry; rewrite deno_app_elim, deno_cond_elim.
   rewrite <-(HI1 H0).
   apply not_is_true_false in H6; rewrite H6, deno_nil_elim; trivial.

   eapply eequiva_weaken; 
    [ | | | | apply equiv_eequiva; apply equiv_assert with (P:=I)]; trivial.
   unfold implMR, andR; intros ? m1 m2 [ [ [? ?] ?] ?]; repeat split; trivial.
   apply HI2; trivial.
   unfold implMR, andR; intuition.
  Qed.

  Lemma split_unroll_second_asym: forall (n a:nat) lam,
   (forall k, 1 <= lam k)%R ->
   (forall k, ProdRR lam1 a n * lam2 <= lam k)%R ->
   decMR I ->
   eequiva
   ((I /-\ EP1 (i =?= a)) /-\ ~- EP1 P1)
   E1 (unroll_while b1 c1 n ++ [Assert P1])
   E2 (unroll_while b2 c2 n ++ [Assert P2])
   I
   lam (fun k => 0).  
  Proof.
   induction n; intros.

   simpl unroll_while.
   eapply eequiva_weaken with
    (lam':=fun k => (1 * 1)%R)
    (ep':= fun k => 0 + _ ** 0); 
    [ | | | | apply eequiva_seq with (I /-\ ~- EP1 P1)].
   trivial.
   trivial.
   intros; rewrite Rmult_1_l; trivial.
   intros ?; rewrite multRU_0_r; auto.
   trivial.

   apply eequiva_cond.
   trivial.
   eapply eequiva_weaken; [ | | | | apply eequiva_nil]; trivial.
   unfold implMR, andR; intuition.
   eapply eequiva_weaken; [ | | | | apply eequiva_nil]; trivial.
   unfold implMR, andR; intuition.
   intros ? ? ? [ [? _] _]; apply HI1; trivial.

   apply equiv_eequiva.
   eapply equiv_sub; [ | | apply equiv_assert with (P:=I)].
   intros ? ? ? [? ?]; split; [ | apply HI2 ]; trivial.
   unfold andR; intuition.
   
   (* Inductive case *)
   simpl unroll_while.
   apply eequiva_case with (EP1 b1).
   trivial.
   
   apply eequiva_eq_compat_l with
    (c1 ++ (unroll_while b1 c1 n ++ [Assert P1])).
   intros ? ? ? ? [ [ [? _] _] ?].
   rewrite deno_app_elim, deno_app_elim.
   rewrite deno_cond_t_elim; trivial.
   rewrite deno_app_elim.
   apply mu_stable_eq; refine (ford_eq_intro _); intros.
   rewrite deno_app_elim; trivial.

   apply eequiva_eq_compat_r with
    (c2 ++ (unroll_while b2 c2 n ++ [Assert P2])).
   intros ? ? ? ? [ [ [? _] _] ?].
   rewrite deno_app_elim, deno_app_elim.
   rewrite deno_cond_t_elim; trivial.
   rewrite deno_app_elim.
   apply mu_stable_eq; refine (ford_eq_intro _); intros.
   rewrite deno_app_elim; trivial.
   apply HI1 in H4.
   unfold EP_eq_expr in H4; rewrite <-H4; trivial.

   eapply eequiva_weaken with
    (lam':=fun k => Rmax (lam2 * ProdRR lam1 a (S n)) 
                         (ProdRR lam1 a (S n) * lam2) )
    (ep':=fun k => _) ;
    [ | | | | eapply eequiva_assert_app with P1 P2].
   trivial.
   trivial.
   intros; apply Rmax_case; trivial.
   rewrite Rmult_comm; trivial.
   trivial.
   intros; rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; trivial.
   fourier.
   fourier.
   apply ProdRR_ge_1; trivial.
   intros; rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; trivial.
   fourier.
   fourier.
   apply ProdRR_ge_1; trivial.
   
   auto.

   rewrite app_assoc, (app_assoc c2).
   eapply eequiva_weaken with
    (lam':=fun k => (lam2 * ProdRR lam1 (S a) n)%R)
    (ep':=fun k => 0 + _ ** 0);
    [ | | | | apply eequiva_seq with (I /-\ EP1 (i =?= S a) /-\ EP1 P1) ].
   trivial.
   trivial.
   intros; apply Rmult_le_compat; trivial.
   fourier.
   rewrite <-ProdRR_ge_1; trivial; fourier.

   simpl.
   rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; trivial.
   fourier.
   rewrite <-ProdRR_ge_1; trivial; fourier.
  
   intros ?; rewrite multRU_0_r, Uplus_zero_left; trivial.
   intro; apply ProdRR_ge_1; trivial.
   
   eapply eequiva_weaken; [ | | | | apply (H2 a)].
   unfold implMR, andR; intuition.
   apply not_is_true_false in H7.
   unfold EP1; rewrite eval_negb, H7; trivial.
   unfold implMR, andR; intuition.
   trivial.
   trivial.

   eapply eequiva_weaken; [ | | | | apply (split_unroll_last_asym n (S a))].
   unfold implMR, andR; intuition.
   trivial.
   intros; apply Rle_refl.
   trivial.
   intros; simpl; apply ProdRR_ge_1; trivial.

   rewrite app_assoc, (app_assoc c2).
   eapply eequiva_weaken with
    (lam':=fun k => (lam1 a * (ProdRR lam1 (S a) n * lam2))%R)
    (ep':=fun k => 0 + _ ** 0);
    [ | | | | apply eequiva_seq with (I /-\ EP1 (i =?= S a) /-\ EP1 (!P1)) ].
   trivial.
   trivial.
   intros; simpl.
   rewrite <-Rmult_assoc, Rmult_comm; trivial.
   intros ?; rewrite multRU_0_r, Uplus_zero_left; trivial.
   intros; rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; trivial.
   fourier.
   fourier.
   apply ProdRR_ge_1; trivial.

   eapply eequiva_weaken;
    [ | | | | apply (H1 a)].
   unfold implMR, andR; intuition.
   apply not_is_true_false in H7.
   unfold EP1; rewrite eval_negb, H7; trivial.
   unfold implMR, andR; intuition.
   trivial.
   trivial.

   eapply eequiva_weaken
    with (lam':=fun k => (ProdRR lam1 (S a) n * lam2)%R); 
     [ | | | | apply (IHn (S a))].
   unfold implMR, andR; intuition.
   unfold EP1 in H7; rewrite eval_negb in H7.
   apply not_is_true_false.
   apply is_true_negb in H7; trivialb.
   trivial.
   intros; trivial.
   trivial.
   intros; rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; trivial.
   fourier.
   fourier.
   apply ProdRR_ge_1; trivial.
   trivial.

   auto.

   apply eequiva_eq_compat_l with [Assert P1].
   intros ? ? ? ? [ [ [? ?] ? ] ?].
   rewrite deno_assert_elim, deno_app_elim, deno_cond_elim.
   apply not_is_true_false in H7; rewrite H7.
   apply not_is_true_false in H6; rewrite H6.
   rewrite deno_nil_elim, deno_assert_elim.
   rewrite H6; trivial.

   apply eequiva_eq_compat_r with [Assert P2].
   intros ? ? ? ? [ [ [? ?] ? ] ?].
   rewrite deno_assert_elim, deno_app_elim, deno_cond_elim.
   rewrite <-(HI1 H4).
   rewrite <-(HI2 H4).
   apply not_is_true_false in H7; rewrite H7.
   apply not_is_true_false in H6; rewrite H6.
   rewrite deno_nil_elim, deno_assert_elim.
   rewrite <-(HI2 H4), H6; trivial.
   
   eapply eequiva_weaken; [ | | | | apply equiv_eequiva]; trivial.
   eapply equiv_sub; [ | | apply equiv_assert with (P:=I)].
   intros ? ? ? [ [ [? ?] ?] _].
   split; trivial.
   apply HI2; trivial.
   unfold andR; intuition.
  Qed.

  Lemma assert_contradiction_asym : forall k b c e n E (m:Mem.t k) f,
   (forall m, EP k e m -> range (EP k e) ([[c]] E m)) ->
   EP k e m ->
   mu ([[ unroll_while b c n ++ [Assert !e] ]] E m) f == 0.
  Proof.
   induction n; intros.
   
   simpl unroll_while.
   rewrite deno_app_elim, deno_cond_elim.
   case (E.eval_expr b m);
    rewrite deno_nil_elim, deno_assert_elim, eval_negb, H0; trivial.

   simpl unroll_while.
   rewrite deno_app_elim, deno_cond_elim.
   case (E.eval_expr b m).
   rewrite deno_app_elim.
   symmetry; apply H; trivial.
   intros.
   rewrite <-deno_app_elim.
   symmetry; apply IHn;  trivial.
 
   rewrite deno_nil_elim, deno_assert_elim.
   rewrite eval_negb, H0; trivial.
  Qed.

  Lemma push_assert_asym: forall k b c e n E (m:Mem.t k) f,
   (forall m, EP k e m -> range (EP k e) ([[c]] E m)) ->
   EP k (!e) m ->
   mu ([[ unroll_while b (c ++ [Assert !e]) n ]] E m) f ==
   mu ([[ unroll_while b c n ++ [Assert !e] ]] E m) f.
  Proof.
   clear; induction n; intros.
   simpl unroll_while.
   rewrite deno_cond_elim.
   symmetry; rewrite deno_app_elim, deno_cond_elim.
   case (E.eval_expr b m);
    rewrite deno_nil_elim, deno_nil_elim, deno_assert_elim, H0; trivial.
 
   simpl unroll_while.
   rewrite deno_cond_elim.
   symmetry; rewrite deno_app_elim, deno_cond_elim.
   case (E.eval_expr b m).
   2:rewrite deno_nil_elim, deno_nil_elim, deno_assert_elim, H0; trivial.

   rewrite deno_app_elim, deno_app_elim, deno_app_elim.
   transitivity 
    (mu ([[c]] E m)
     (fun m' =>
      if EP k (!e) m' then 
       mu ([[ unroll_while b c n ]] E m')
           (fun m'' => mu ([[ [Assert !e] ]] E m'') f)
    else 0)).
   apply mu_stable_eq.
   refine (ford_eq_intro _); intro m'.
   case_eq (EP k (!e) m'); intro He.
   trivial.
   rewrite <-deno_app_elim.
   apply assert_contradiction.
   trivial.
   unfold EP in He; rewrite eval_negb in He.
   apply negb_false_iff in He; trivial.

   apply mu_stable_eq.
   refine (ford_eq_intro _); intro m'.
   rewrite deno_assert_elim.
   unfold EP.
   case_eq (@E.eval_expr k T.Bool (!e) m').
   symmetry.
   rewrite <-deno_app_elim.
   apply IHn.
   trivial.
   trivial.
   trivial.
  Qed.

  Lemma split_unroll_le_lift_asym : forall (n a:nat) lam,
   (forall k, 1 <= lam k)%R ->
   (forall k j, (j <= n)%nat -> (ProdRR lam1 a j * lam2 <= lam k)%R) ->
   decMR I ->
   eequiva ((I /-\ EP1 (i =?= a)) /-\ ~- EP1 P1)
   E1 (unroll_while b1 c1 n ++ [Assert !b1])
   E2 (unroll_while b2 c2 n ++ [Assert !b2])
   I
   lam (fun k => 0).  
  Proof.
   intros n a lam HI Hge Hle.
   eapply eequiva_seq_weaken with 
    (lam1:=fun k => lam k) (ep1:=fun _ => 0) 
    (lam2:=fun k => 1%R)   (ep2:=fun _ => 0).
   trivial.
   intros; rewrite Rmult_1_r; trivial.
   intros ?; rewrite multRU_0_r, Uplus_zero_left; trivial.

   eapply eequiva_weaken with (lam':=fun k => _);
    [ | | | | apply eequiva_assert_join with (e1:=P1) (e2:=P2)]; trivial.
   intro; rewrite Rmax_left; trivial.   

   apply (split_unroll_second_asym n a lam); trivial.
   auto.

   apply eequiva_eq_compat_l with
    (unroll_while b1 (c1 ++ [Assert !P1]) n).
   intros.
   apply push_assert.
   intros; apply range_c1; trivial.
   destruct H as [_ ?].
   apply not_is_true_false in H.
   unfold EP; rewrite eval_negb; trivial.
   rewrite H; trivial.

   apply eequiva_eq_compat_r with
    (unroll_while b2 (c2 ++ [Assert !P2]) n).
   intros.
   apply push_assert_asym.
   intros; apply range_c2; trivial.
   destruct H as [ [? _] ?].
   apply HI2 in H.
   apply not_is_true_false in H0.
   unfold EP; rewrite eval_negb; trivial.
   unfold EP_eq_expr in H; rewrite H in H0; rewrite H0; trivial.

   apply split_unroll_first_asym; trivial.
 
   intro; transitivity (ProdRR lam1 a n * lam2)%R; [ | auto].
   rewrite <-Rmult_1_r at 1. 
   apply Rmult_le_compat; [ | fourier | auto | fourier].
   rewrite <-ProdRR_ge_1; [fourier | auto].
   auto.
  
   apply equiv_eequiva. 
   eapply equiv_sub; [ | | apply equiv_assert with (P:=I)].
   intros; split; trivial.
   rewrite eval_negb, eval_negb.
   rewrite (HI1 H); trivial.
   unfold andR; intuition.
  Qed.
 
  Lemma eequiva_while_split : forall lam (a n:nat),
   (forall k, 1 <= lam k)%R ->
   (forall k j, (j <= n)%nat -> ProdRR lam1 a j * lam2 <= lam k)%R ->
   decMR I ->
   (forall k (m1 m2:Mem.t k), 
    I m1 m2 -> 
    [[ [while b1 do c1] ]] E1 m1 == 
    drestr ([[ unroll_while b1 c1 n ]] E1 m1) (negP (EP k b1)) /\
    [[ [while b2 do c2] ]] E2 m2 == 
    drestr ([[ unroll_while b2 c2 n ]] E2 m2) (negP (EP k b2))) ->
   eequiva
    (I /-\ EP1 (i =?= a) /-\ EP1 (!P1))
    E1 [ while b1 do c1 ]
    E2 [ while b2 do c2 ]
    (I /-\ EP1 (!b1))
    lam (fun k => 0).
  Proof.
   intros.
   apply eequiva_eq_compat_l with [while b1 do c1; Assert !b1].
   intros ? ? ? ? [? [? ?] ].
   rewrite deno_cons_elim, Mlet_simpl.
   symmetry; rewrite deno_while_restr_elim.
   apply mu_stable_eq.
   refine (ford_eq_intro _); intros ?.
   rewrite deno_assert_elim, eval_negb; case (E.eval_expr b1 n0); trivial.

   apply eequiva_eq_compat_r with [while b2 do c2; Assert !b2].
   intros ? ? ? ? [? [? ?] ].
   rewrite deno_cons_elim, Mlet_simpl.
   symmetry; rewrite deno_while_restr_elim.
   apply mu_stable_eq.
   refine (ford_eq_intro _); intros ?.
   rewrite deno_assert_elim, eval_negb; case (E.eval_expr b2 n0); trivial.
 
   repeat match goal with 
    |- context [ [?i1; ?c1] ] => change [i1; c1] with ([i1] ++ [c1])
   end.
   eapply eequiva_weaken with
    (lam':=fun k => (lam k * 1)%R)
    (ep' :=fun k => 0 + _ ** 0);
    [ | | | | apply eequiva_seq with I ].
   trivial.
   trivial.
   intro; rewrite Rmult_1_r; trivial.
   intros ?; rewrite multRU_0_r, Uplus_zero_left; trivial.
   trivial.

   unfold eequiva; intros.
   destruct (@split_unroll_le_lift_asym n a lam H H0 X k0 m1 m2) as [d Hd].
   exists d; intros [? [? ?] ].
   destruct (H4 _ _ _ H5).
   eapply le_lift_asym_eq_compat.
   reflexivity.
   symmetry; apply H8.
   symmetry; apply H9.
   reflexivity.
   reflexivity.
   
   refine (le_lift_asym_eq_compat _ _ _ _ _ (Hd _)); trivial.

   apply eq_distr_intro; intro f.
   unfold drestr; rewrite deno_app_elim, Mlet_simpl.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
   rewrite deno_assert_elim, eval_negb.
   unfold negP, EP; case (E.eval_expr b1 m'); trivial.

   apply eq_distr_intro; intro f.
   unfold drestr; rewrite deno_app_elim, Mlet_simpl.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
   rewrite deno_assert_elim, eval_negb.
   unfold negP, EP; case (E.eval_expr b2 m'); trivial.

   unfold andR; intuition.
   apply is_true_negb; unfold EP1 in H7; rewrite eval_negb in H7; trivial.

   apply equiv_eequiva.
   eapply equiv_sub; [ | | apply equiv_assert].
   intros; split.
   eexact H5.
   rewrite eval_negb, eval_negb; apply HI1 in H5; unfold EP_eq_expr in H5.
   rewrite H5; trivial.
   unfold andR; intuition.  
  Qed.

 End SPLIT_WHILE_ASYM.

End Asymm_Logic.


End Make.

