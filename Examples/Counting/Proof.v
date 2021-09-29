Require Export Extension.

Open Scope positive_scope.

Parameter E0 : env.

Parameter delta: forall (k:nat), nat.

Definition Pre (In:Var.var (T.List T.Zt)) : mem_rel := 
 fun k (m1 m2:Mem.t k) =>
  length (m1 In) = length (m2 In) /\
  Zlist_ApEq (m1 In) (m2 In) /\
  DiffBound (m1 In) (m2 In) (delta k).

Lemma dep_Pre: forall X, depend_only_rel (Pre X) {{X}} {{X}}.
Proof.
 unfold Pre; intros X k m1 m2 m1' m2' H1 H2 (H3,(H4,H5)); 
  repeat split; rewrite <-(H1 _ X), <-(H2 _ X); auto with set.
Qed.

Lemma dec_Pre: forall L, decMR (Pre L).
Proof.
 unfold Pre; intros L k m1 m2.
 set (Ib := nat_eqb (length (m1 L)) (length (m2 L)) &&
  Zlist_ApEqb (m1 L) (m2 L) && 
  DiffBoundb (m1 L) (m2 L) (delta k)).
 case_eq Ib; unfold Ib, is_true; intro H; [ left | right ]; clear Ib.
 repeat rewrite andb_true_iff in H; destruct H as ((H1,H2),H3).
 repeat split.
 apply (nat_eqb_true H1).
 rewrite <-Zlist_ApEqb_iff; apply H2.
 rewrite <-DiffBoundb_iff; apply H3.
 intro H'.
 rewrite 2 andb_false_iff in H; destruct H' as (?,(?,?));
  destruct H as [ [ ? | ? ] | ? ].
 rewrite H0 in H.
 apply (eq_true_false_abs _ (nat_eqb_refl (length (m2 L))) H).
 rewrite <-Zlist_ApEqb_iff in H1.
 apply (eq_true_false_abs _ H1 H).
 rewrite <-DiffBoundb_iff in H2.
 apply (eq_true_false_abs _ H2 H).
Qed.

Lemma Pre_refl: forall L k (m:Mem.t k), Pre L _ m m.
Proof.
 intros L k m; repeat split.
 apply (list_ApEq_eq nZeq_bool_spec (eq_refl _)).
 apply (DiffBound_eq _ (eq_refl _)).
Qed.

Definition Post (T:T.type) (Out:Var.var T) : mem_rel := kreq_mem {{Out}}.

Implicit Arguments Post [T].


Section LAPLACE_MECHANISM.

Lemma Laplace_dist: forall a1 a2 eps,
  (0 < eps)%R ->
  le_dist (Laplace eps a1) (Laplace eps a2)
    (exp (eps * INR (Zabs_nat (a1 - a2)))) (@D0 U).
Proof.
 intros.
 eapply le_dist_weaken_ep; [ | eapply le_dist_discr_pointwise_ub with 
   (F:=fun _ => @D0 U) (G:=fun _ => @D0 U) 
   (AeqU:= fun (a y:Z) => B2U (Zeq_bool y a))
   (p:= parity_split (D_points (Laplace_Discrete eps a1)) 
     (D_points (Laplace_Discrete eps a2))) ].
   rewrite serie_zero; auto.
   intro a; eapply cover_eq_stable; [ apply (@carT_cover 0%nat T.Zt) | ].
     unfold carT; simpl; refine (ford_eq_intro _); intro z;
       rewrite Zeq_bool_comm; trivial.
   rewrite <-exp_0; apply exp_monotonic;
     apply (Rmult_le_pos _ _ (Rlt_le _ _ H) (pos_INR _)).
   apply disc_eqpoint_l.
   apply disc_eqpoint_r.

 intro a.
 apply Uplus_le_perm_left; rewrite Uplus_zero_right.
 apply multRU_le_Rmult.
   apply (Rlt_le _ _ (exp_pos _)).
 rewrite Rmult_comm, (Laplace_ratio H a1 a2 a).
 apply (Rmult_le_compat_l _ _ _ (iR_ge_0 _)).
 apply exp_monotonic; apply (Rmult_le_compat_l _ _ _ (Rlt_le _ _ H)).
 rewrite <-minus_IZR, Rabs_Zabs, INR_IZR_INZ;
  apply IZR_le; rewrite <-inj_Zabs_nat; apply inj_le; trivial.

 intro a.
 apply Uplus_le_perm_left; rewrite Uplus_zero_right.
 apply multRU_le_Rmult.
   apply (Rlt_le _ _ (exp_pos _)).
 rewrite Rmult_comm, (Laplace_ratio H a2 a1 a).
 apply (Rmult_le_compat_l _ _ _ (iR_ge_0 _)).
 apply exp_monotonic; apply (Rmult_le_compat_l _ _ _ (Rlt_le _ _ H)).
 rewrite <-Ropp_minus_distr, <-minus_IZR, Rabs_Ropp, Rabs_Zabs, INR_IZR_INZ;
   apply IZR_le; rewrite <-inj_Zabs_nat; apply inj_le; trivial.
 Qed.


 Variable E1 E2 : env.
 Variable a1 : Var.var T.Zt.
 Variable a2 : Var.var T.Zt.
 Variable r : Var.var T.Zt.

 Lemma Lap_Mech: eequiv 
  (fun k (m1 m2:Mem.t k) => (Zabs_nat (m1 a1 - m2 a2)%Z <= delta k)%nat)
  E1 [ r <$- Lap  a1 ]
  E2 [ r <$- Lap  a2 ]
  (kreq_mem {{r}}) 
  (fun k => exp (Eps k * INR (delta k))) (fzero _).
 Proof.
  intros.
  apply eequiv_weaken with 
   (fun k (m1 m2:Mem.t k) => (Zabs_nat (m1 a1 - m2 a2)%Z <= delta k)%nat)
   (EP_eq_expr r r) 
   (fun k => exp (Eps k * INR (delta k))) (fzero _); trivial.
  unfold EP_eq_expr; intros k m1 m2 Hm t v Hv; 
   Vset_mem_inversion Hv; subst; auto.
  refine (@eequiv_random_discr _ _ _ _ _ _ _ _ _ (fzero nat) _ _);
    [ auto | ].
  intros; unfold DE.eval_support, US.eval, fzero; simpl.
  eapply le_dist_weaken; [ | | apply Laplace_dist ]; trivial.
   split.
     apply (Rlt_le _ _ (exp_pos _)).
     apply exp_monotonic, Rmult_le_compat_l. 
       apply (Rlt_le _ _ (eps_pos _)).
       auto with real.
       apply eps_pos.
 Qed.

End LAPLACE_MECHANISM.



(* LAPLACE MECHANISM OVER VECTORS *)
Section LIST_LAPLACE_MECHANISM.

 Variable E1 E2 : env.

 Variable L1 L2 Y : Var.var (T.List T.Zt).

 Lemma ListLap_Mech: eequiv 
  (fun k (m1 m2:Mem.t k) => 
   length (m1 L1) = length (m2 L2) /\ 
   Zlist_ApEq (m1 L1) (m2 L2) /\ 
   DiffBound (m1 L1) (m2 L2) (delta k))
  E1 [ Y <$- MapLap eps L1 ]
  E2 [ Y <$- MapLap eps L2 ]
  (kreq_mem {{Y}}) 
  (fun k => exp (Eps k * INR (delta k))) (fzero _).
 Proof.
  intros.
  assert (Haux: forall k, (1 <= exp (Eps k * INR (delta k)))%R) by 
    (intro; rewrite <-exp_0; apply exp_monotonic;
      apply (Rmult_le_pos _ _ (Rlt_le _ _ (eps_pos k)) (pos_INR _))).
  match goal with |- eequiv ?P _ _ _ _ ?Q ?Lam ?Eps => 
   apply eequiv_weaken with P (EP_eq_expr Y Y) Lam Eps; trivial end.
  unfold EP_eq_expr; intros k m1 m2 Hm t v Hv; 
   Vset_mem_inversion Hv; subst; auto.
  refine (eequiv_random_discr _ _ _ _ _ _ _ _ (fzero nat) _ _); 
    [ auto | ].
  intros; simpl.
  generalize (m1 L1) (m2 L2) H; clear H m1 m2; simpl. 
   intros l1 l2  (H1,(H2,H3)). 
  generalize H1 H2 H3; generalize l2; 
   clear H1 H2 H3 l2; induction l1; intros.
  (* base case *)
  destruct l2; [ simpl; unfold fzero | discriminate ].
  apply le_dist_weaken with R1 (@D0 U); trivial.
    split; [ fourier | auto ].
    apply le_dist_nul; trivial.
  (* inductive case *)
  Opaque eqb_list Zeq_bool Laplace.
  destruct l2; [ discriminate | ].
  generalize  (Zeq_bool_if a z); case_eq (Zeq_bool a z); 
   intros _ Haz'.
  (* a = z *)
  rewrite <-Haz' in *; simpl.
  apply le_dist_Mlet.
  apply IHl1. 
    apply (eq_add_S _ _ H1).
    apply (@list_ApEq_tl_compat Z (fun a b => negb (Zeq_bool a b)) _ _ H1 H2).
    apply (DiffBound_tl_compat H3).
  (* a <> z *)
  pose proof (@list_ApEq_hd_neq _ _ (0%Z) nZeq_bool_spec _ _  H1 H2 Haz');
   simpl in H.
  rewrite <-H in *.
  simpl ListLaplace; unfold fzero.
  eapply le_dist_Mlet_right.
    apply (carT_cover k (T.List T.Zt)).
    apply ListLaplace_Discrete.
    auto.
  intro l; apply le_dist_Mlet.
  eapply le_dist_weaken; [ | | apply Laplace_dist ]; trivial.
   split.
     apply (Rlt_le _ _ (exp_pos _)).
     apply exp_monotonic, Rmult_le_compat_l. 
       apply (Rlt_le _ _ (eps_pos _)).
       apply (le_INR _ _ (@H3 0%nat (lt_0_Sn _))).
       apply eps_pos.
 Qed.

End LIST_LAPLACE_MECHANISM.


Notation sum    := (Var.Lvar T.Zt  100).
Notation ret    := (Var.Lvar T.Zt  101).
Notation In     := (Var.Lvar (T.List T.Zt) 102).
Notation L      := (Var.Lvar (T.List T.Zt) 103).
Notation Out    := (Var.Lvar (T.List T.Zt) 104).
Notation Y      := (Var.Lvar (T.List T.Zt) 105).
Notation Y'     := (Var.Lvar (T.List T.Zt) 106).

Notation In'    := (Var.Gvar (T.List T.Zt) 201).
Notation Out'   := (Var.Gvar (T.List T.Zt) 202).
Notation c      := (Var.Gvar T.Zt  203).
Notation t      := (Var.Gvar T.Zt  204).


Notation   PrivSum := (Proc.mkP 1 (T.List T.Zt :: nil) T.Zt).

Definition PrivSum_params : var_decl (Proc.targs PrivSum) := dcons _ In (dnil _).

Definition PrivSum_ret : E.expr T.Zt := ret. 

(* Compute the last partial sum and returns a noisy version of it *) 
Definition PrivSumBody := 
 ([ sum <- 0%Z ] ++
 [
  while (0%nat <=! Elen In) do
  [
    sum <- sum +Z Ehead In;
    In <- Etail In
  ] ]) ++ 
 [ ret <$- Lap sum ].

Notation   PPS2 := (Proc.mkP 2 (T.List T.Zt :: nil) (T.List T.Zt)).

Definition PPS2_params : var_decl (Proc.targs PPS2) := dcons _ In (dnil _).

Definition PPS2_ret : E.expr (T.List T.Zt) := Out. 
 
Definition PPS2_loop_body := 
 [
  sum <- Ehead Y' +Z sum;
  Out <- Out |++| (sum |::| Nil _);
  Y'  <- Etail Y'
  ].

(* Add noise to each entry of the array and output every 
   partial sum of this sanitized version of the array *)
Definition PPS2Body := 
 [ Y' <$- MapLap eps In ] ++
 ([ sum <- 0%Z; Out <- Nil _] ++ 
  [ while (0%nat <! Elen Y') do PPS2_loop_body ]).

Definition E :=  
 let E_PS := 
  add_decl E0 PrivSum PrivSum_params (refl_equal true) PrivSumBody PrivSum_ret in
 let E_PPS2 := 
 add_decl E_PS PPS2 PPS2_params (refl_equal true) PPS2Body PPS2_ret in E_PPS2.

Definition iEE := 
 add_refl_info PPS2 (add_refl_info PrivSum (empty_info E E)).

Open Scope nat_scope.


(* ******************************************************************* *)
(* *************************** PRIVATE SUM *************************** *)
(* ******************************************************************* *)

Lemma PrivSumBody_diff_private: 
 eequiv (Pre In)
 E PrivSumBody 
 E PrivSumBody
 (Post ret)
 (fun k => exp (Eps k * INR (delta k))) 
 (fun _ => D0).
Proof.
 apply equiv_seq_eequiv with (fun k (m1 m2: Mem.t k) =>
  Zabs_nat (m1 sum - m2 sum) <= delta k); auto.
 set (I := req_mem_rel Vset.empty (fun k (m1 m2:Mem.t k), 
  length (m1 In) = length (m2 In) /\ 
  DiffBound (m1 In) (m2 In) (delta k) /\
  (m1 sum <> m2 sum ->  m1 In = m2 In /\ Zabs_nat (m1 sum - m2 sum) <= delta k) /\
  (m1 sum = m2 sum -> Zlist_ApEq (m1 In) (m2 In)))).
 (* assertion upon the loop entry *)
 apply equiv_app with (Q:=I).
 unfold I; eqobsrel_tail; simpl; intros k m1 m2 (H1,(H2,H3)).
 split; [ | mem_upd_simpl; repeat split ]; trivial.
 apply req_mem_empty.
 exfalso; auto with arith.
 exfalso; auto with arith.
 (* loop rule *) 
 eapply equiv_weaken; [ | apply equiv_while ].
 intros k m1 m2 ((_,(_,(_,(H1,H2)))),_).
 destruct (Z_eq_dec (m1 sum) (m2 sum)) as [ Heq | Heq ].
 rewrite Heq, Zminus_diag; apply le_0_n.
 apply (proj2 (H1 Heq)).
 intros k m1 m2 (_,(H,_)); expr_simpl.
 (* proof of loop invariant *)  
 unfold I; eqobsrel_tail; simpl; intros k m1 m2; 
  expr_simpl; intro H; decompose [and] H; repeat split.
 auto with list_op.
 auto with list_op.
 destruct (Z_eq_dec (m1 sum) (m2 sum)) as [ Heq | Heq ].
 rewrite Heq in H3.
 apply (list_ApEq_hd_neq nZeq_bool_spec H1 (H6 Heq) 
  (Zplus_diff_eq_compat_l H3)).
 rewrite (proj1 (H4 Heq)); trivial.
 destruct (Z_eq_dec (m1 sum) (m2 sum)) as [ Heq | Heq ].
 (* same sum *)
 rewrite Heq.
 replace (m2 sum + hd 0%Z (m1 In) - (m2 sum + hd 0%Z (m2 In)))%Z
  with (hd 0%Z (m1 In) - hd 0%Z (m2 In))%Z by ring.
 destruct (m1 In); destruct (m2 In); try discriminate; simpl.
 apply le_0_n.
 apply (H2 0 (lt_0_Sn _)).
 (* diff sum *)
 rewrite (proj1 (H4 Heq)).
 replace (m1 sum + hd 0%Z (m2 In) - (m2 sum + hd 0%Z (m2 In)))%Z
  with (m1 sum - m2 sum)%Z by ring.
 apply (proj2 (H4 Heq)).
 intro.
 destruct (Z_eq_dec (m1 sum) (m2 sum)) as [ Heq | Heq ].
 apply (list_ApEq_tl_compat H1 (H6 Heq)).
 apply (list_ApEq_eq nZeq_bool_spec).
 apply (f_equal _ (proj1 (H4 Heq))).
 (* application of Laplace-sampling rule to conclude *)
 apply Lap_Mech.
Qed.

Lemma PrivSum_diff_private: 
 eequiv
 (Pre L)
 E [  t <c- PrivSum with {L} ]
 E [  t <c- PrivSum with {L} ]
 (Post t)
 (fun k => exp (Eps k * INR (delta k))) 
 (fun _ => D0).
Proof.
 set (c':= (In <- L) :: (PrivSumBody ++ [ t <- ret ])).
 apply eequiv_trans_l with (c2:=c') (E2:=E) 
  (P1:=kreq_mem {{L}}) (Q1:=kreq_mem {{t}}) (Q2:=kreq_mem {{t}}) 
  (ep1:=fun _ => D0) (lam1:=fun _ => R1)
  (ep2:=fun _ => D0) (lam2:= fun k => exp (Eps k * INR (delta k))).
 trivial.
 trivial.
 intros; rewrite Rmult_1_l; trivial.
 intros; apply max_le; rewrite Uplus_zero_left, multRU_0_r; trivial.
 apply dec_Pre.
 intros k m1 m2 _; apply req_mem_refl.
 apply req_mem_trans.
 auto with real.
 intros; repeat (multRU_simpl || Usimpl); auto.
 apply equiv_eequiv.
 sinline iEE PrivSum.
 alloc_l t ret; eqobs_in. 
 apply eequiv_trans_r with (c2:=c') (E2:=E) 
  (P2:=kreq_mem {{L}}) (Q1:=kreq_mem {{t}}) (Q2:=kreq_mem {{t}}) 
  (ep1:=fun _ => D0) (lam1:= fun k => exp (Eps k * INR (delta k)))
  (ep2:=fun _ => D0) (lam2:=fun _ => R1).
 trivial.
 trivial.
 intros; rewrite Rmult_1_l; trivial.
 intros; apply max_le; rewrite Uplus_zero_left, multRU_0_r; trivial.
 apply dec_Pre.
 intros k m1 m2 _; apply req_mem_refl.
 apply req_mem_trans.
 apply eequiv_cons_equiv with (Pre In); [ auto | | ].
 eapply equiv_strengthen; [ | apply equiv_assign ];
  intros k m1 m2 ?; unfold upd_para, Pre; mem_upd_simpl.
 apply eequiv_seq_equiv with (kreq_mem {{ret}}); 
  [ auto | apply PrivSumBody_diff_private | eqobs_in ].
 apply equiv_eequiv.
 sinline iEE PrivSum. 
 alloc_r t ret; eqobs_in.
Qed.

 
(* ******************************************************************* *)
(* ********************** PRIVATE PARTIAL SUM 2 ********************** *)
(* ******************************************************************* *)
Lemma PPS2Body_diff_private: 
 eequiv 
 (Pre In) 
 E PPS2Body 
 E PPS2Body 
 (Post Out) 
 (fun k => exp (Eps k * INR (delta k))) (fzero _).
Proof.
 unfold PPS2Body.
 eapply eequiv_seq_equiv with (kreq_mem {{Y'}}); [ auto | | ].
 apply eequiv_weaken with (5:=ListLap_Mech _ _ _ _ _); trivial.
 apply equiv_app with (kreq_mem {{Y',sum,Out}}).
 eqobs_in.
 eapply equiv_weaken; [ | apply equiv_while ].
 intros k m1 m2 (H,_); apply req_mem_weaken with (2:=H); apply eq_refl.
 intros; apply depend_only_fv_expr; apply req_mem_weaken with (2:=H);
 apply eq_refl.
 eqobs_in.
Qed.

Lemma PPS2_diff_private: 
 eequiv
 (Pre L)
 E [ Y <c- PPS2 with {L} ]
 E [ Y <c- PPS2 with {L} ]
 (Post Y)
 (fun k => exp (Eps k * INR (delta k))) 
 (fun _ => D0).
Proof.
 set (c':= (In <- L) :: (PPS2Body ++ [ Y <- Out ])).
 apply eequiv_trans_l with (c2:=c') (E2:=E) 
  (P1:=kreq_mem {{L}}) (Q1:=kreq_mem {{Y}}) (Q2:=kreq_mem {{Y}}) 
  (ep1:=fun _ => D0) (lam1:=fun _ => R1)
  (ep2:=fun _ => D0) (lam2:= fun k => exp (Eps k * INR (delta k))).
 trivial.
 trivial.
 intros; rewrite Rmult_1_l; trivial.
 intros; apply max_le; rewrite Uplus_zero_left, multRU_0_r; trivial.
 apply dec_Pre.
 intros k m1 m2 _; apply req_mem_refl.
 apply req_mem_trans.
 auto with real.
 intros; repeat (multRU_simpl || Usimpl); auto.
 apply equiv_eequiv.
 alloc_l Y Out'.
 alloc_r Out Out'.
 inline_l iEE PPS2.
 eqobs_ctxt.
 ep; deadcode.
 eqobs_in.

 apply eequiv_trans_r with (c2:=c') (E2:=E) 
  (P2:=kreq_mem {{L}}) (Q1:=kreq_mem {{Y}}) (Q2:=kreq_mem {{Y}}) 
  (ep1:=fun _ => D0) (lam1:= fun k => exp (Eps k * INR (delta k)))
  (ep2:=fun _ => D0) (lam2:=fun _ => R1).
 trivial.
 trivial.
 intros; rewrite Rmult_1_l; trivial.
 intros; apply max_le; rewrite Uplus_zero_left, multRU_0_r; trivial.
 apply dec_Pre.
 intros k m1 m2 _; apply req_mem_refl.
 apply req_mem_trans.
 auto with real.
 intros; repeat (multRU_simpl || Usimpl); auto.
 apply eequiv_cons_equiv with (Pre In); [ auto | | ].
 eapply equiv_strengthen; [ | apply equiv_assign ];
  intros k m1 m2 ?; unfold upd_para, Pre; mem_upd_simpl.
 apply eequiv_seq_equiv with (kreq_mem {{Out}}); 
  [ auto | apply PPS2Body_diff_private | eqobs_in ].
 apply equiv_eequiv.
 alloc_r Y Out'.
 alloc_l Out Out'.
 inline_r iEE PPS2.
 eqobs_ctxt.
 ep; deadcode.
 eqobs_in.
Qed.


(* ************************************************************ *)
(* ************************ SMART SUM  ************************ *)
(* ************************************************************ *)

Definition SmartMech :=
 [ c <- 0%Z; Out' <- Nil _; t <- 0%Z ] ++
 [
  while (0%nat <! Elen In') do 
   [
    L <- Efirstn In';
    Y <c- PPS2 with {L};
    t <c- PrivSum with {L};
    Out' <- Out' |++| ((E.Eop (O.Ouser OMapPlus)) {c,Y}); 
    c <- c +Z  t;
    In' <- Elastn In'
   ]
 ]. 


Definition I := req_mem_rel {{Out',c}} 
 (fun k (m1 m2:Mem.t k), 
  length (m1 In') = length (m2 In') /\ 
  DiffBound (m1 In') (m2 In') (delta k) /\
  Zlist_ApEq (m1 In') (m2 In')).

Lemma dep_I: depend_only_rel I 
 (Vset.union {{Out',c}} {{In'}})
 (Vset.union {{Out',c}} {{In'}}).
Proof.
 unfold I. 
 apply depend_only_req_mem_rel.
 intros k m1 m2 m1' m2' H1 H2 (H3,(H4,H5)); repeat split.
 rewrite <-(H1 _ In'), <-(H2 _ In'); auto with set.
 rewrite <-(H1 _ In'), <-(H2 _ In'); auto with set.
 rewrite <-(H1 _ In'), <-(H2 _ In'); auto with set.
Qed.

Lemma dec_I: decMR I.
Proof.
 apply decMR_req_mem_rel.
 intros k m1 m2.
 set (Ib := nat_eqb (length (m1 In')) (length (m2 In')) &&
  DiffBoundb (m1 In') (m2 In') (delta k) &&
  Zlist_ApEqb (m1 In') (m2 In')).
 case_eq Ib; unfold Ib, is_true; intro H; [ left | right ]; clear Ib.
 repeat rewrite andb_true_iff in H; destruct H as ((H1,H2),H3).
 repeat split.
 apply (nat_eqb_true H1).
 rewrite <-DiffBoundb_iff; apply H2.
 rewrite <-Zlist_ApEqb_iff; apply H3.
 intro H'.
 rewrite 2 andb_false_iff in H; destruct H' as (?,(?,?));
  destruct H as [ [ ? | ? ] | ? ].
 rewrite H0 in H.
 apply (eq_true_false_abs _ (nat_eqb_refl (length (m2 In'))) H).
 rewrite <-DiffBoundb_iff in H1.
 apply (eq_true_false_abs _ H1 H).
 rewrite <-Zlist_ApEqb_iff in H2.
 apply (eq_true_false_abs _ H2 H).
Qed.

Definition iEE_I_empty : eq_inv_info I E E :=
 (@empty_inv_info I _ _ dep_I (eq_refl _) dec_I E E).

Lemma PPS2_I: 
 equiv
 (req_mem_rel {{In}} I) 
 E PPS2Body
 E PPS2Body 
 (req_mem_rel {{Out}} I).
Proof.
 unfold PPS2Body, PPS2_loop_body.
 eqobs_in iEE_I_empty.
Qed.

Lemma PrivSum_I: 
 equiv
 (req_mem_rel {{In}} I) 
 E PrivSumBody
 E PrivSumBody 
 (req_mem_rel {{ret}} I).
Proof.
 unfold PrivSumBody.
 eqobs_in iEE_I_empty.
Qed.

Definition iEE_I :=
 let PPS2_i    := add_info PPS2 Vset.empty Vset.empty iEE_I_empty PPS2_I in
 let Privsum_i := add_info PrivSum Vset.empty Vset.empty PPS2_i PrivSum_I in
  Privsum_i.

Definition I' k (m1 m2:Mem.t k) :=
 length (m1 In') = length (m2 In') /\
 DiffBound (m1 In') (m2 In') (delta k) /\
 Zlist_ApEq (m1 In') (m2 In') /\
 skipn (Lsize k) (m1 In') = skipn (Lsize k) (m2 In').

Lemma dep_I': depend_only_rel I' {{In'}} {{In'}}.
Proof.
 unfold I'.
 intros k m1 m2 m1' m2' H1 H2 (H3,(H4,(H5,H6))); repeat split;
  rewrite <-(H1 _ In'), <-(H2 _ In'); auto with set.
Qed.

Lemma dec_I': decMR I'.
Proof.
 intros k m1 m2.
 set (Ib := nat_eqb (length (m1 In')) (length (m2 In')) &&
  DiffBoundb (m1 In') (m2 In') (delta k) &&
  Zlist_ApEqb (m1 In') (m2 In') &&
  (eqb_list Zeq_bool) (skipn (Lsize k) (m1 In')) (skipn (Lsize k) (m2 In'))).
 case_eq Ib; unfold Ib, is_true; intro H; [ left | right ]; clear Ib.
 repeat rewrite andb_true_iff in H; destruct H as (((H1,H2),H3),H4).
 repeat split.
 apply (nat_eqb_true H1).
 rewrite <-DiffBoundb_iff; apply H2.
 rewrite <-Zlist_ApEqb_iff; apply H3.
 pose proof (eqb_list_spec _ Zeq_bool_if (skipn (Lsize k) (m1 In'))
  (skipn (Lsize k) (m2 In'))); rewrite H4 in H; trivial.
 intro H'.
 rewrite 3 andb_false_iff in H; destruct H' as (?,(?,(?,?)));
  destruct H as [ [ [? | ?] | ? ] | ? ].
 rewrite H0 in H.
 apply (eq_true_false_abs _ (nat_eqb_refl (length (m2 In'))) H).
 rewrite <-DiffBoundb_iff in H1.
 apply (eq_true_false_abs _ H1 H).
 rewrite <-Zlist_ApEqb_iff in H2.
 apply (eq_true_false_abs _ H2 H).
 pose proof (eqb_list_spec _ Zeq_bool_if (skipn (Lsize k) (m1 In'))
  (skipn (Lsize k) (m2 In'))); rewrite H in H4; tauto.
Qed.

Definition iEE_I' : eq_inv_info I' E E := 
 (@empty_inv_info I' _ _ dep_I' (eq_refl _) dec_I' E E).

Lemma SmartMech_diff_private: 
 eequiv
 (Pre In')
 E SmartMech
 E SmartMech
 (Post Out') 
 (fun k => exp (2 * Eps k * INR (delta k))) 
 (fun _ => D0).
Proof.
 assert (Heps: forall k : nat, (1 <= exp (2 * Eps k * INR (delta k)))%R).
 intro k.
 rewrite <-exp_0 at 1; apply exp_monotonic.
 rewrite Rmult_assoc; apply Rmult_le_pos.
 auto with real.
 apply (Rmult_le_pos _ _ (Rlt_le _ _ (eps_pos k)) (pos_INR _)).
 unfold SmartMech at 1.
 apply equiv_seq_eequiv with I; trivial.
 unfold I; eqobsrel_tail; intros k m1 m2 (H1,(H2,H3)); 
  repeat split; expr_simpl; apply req_mem_empty.
 apply eequiv_weaken with I  (I /-\ EP1 (Elen In' =?= 0))
  (fun k => exp (2 * Eps k * INR (delta k))) (fun _ => D0); auto.
 intros k m1 m2 ((H,_),_); apply req_mem_weaken with (2:=H); 
  auto with set.

 (* apply the parallel loop rule *)
 apply Parallel_loop with Lsize; trivial.
 apply Lsize_pos.
 intro k; apply Z_eq_dec.
 intros k m1 m2 (_,(?,_)); trivial.

 (* 1st subgoal *)
 intros k m f Hf.
 match goal with 
  |- _ == fmonot (mu ([[ ?C ]] _ _)) _ => 
   rewrite <-(firstn_skipn 5 C);
   assert (Modify E  {{c,Out',t,Y,L}} (firstn 5 C)) by (apply 
   modify_correct with (refl1_info iEE_I) Vset.empty; apply eq_refl)
 end.
 rewrite deno_app_elim; simpl firstn in *; simpl skipn in *.
 rewrite (Modify_deno_elim H).
 match goal with |- _ == fmonot (mu ?d) _ => rewrite <-(mu_zero d) end.
 apply mu_stable_eq; unfold fzero; refine (ford_eq_intro _); intro m'.
 rewrite deno_assign_elim; apply Hf.
 mem_upd_simpl; expr_simpl.

 (* 2nd subgoal *)
 apply equiv_eequiv.
 apply equiv_cons with (req_mem_rel {{L,c}} I).
 eapply equiv_strengthen; [ | apply equiv_assign ].
 unfold req_mem_rel, andR; intros k m1 m2 H;
  decompose [and] H; clear H; split.
 intros t v Hv; Vset_mem_inversion Hv; subst; mem_upd_simpl.
 apply (proj1 H0); auto with set.
 refine (dep_I _ _ _ _ _ _ _  H0); (apply req_mem_upd_notin_r; 
  [ auto with set | discriminate ]).
 apply equiv_weaken with (req_mem_rel Vset.empty I).
 intros k m1 m2 (_,?); trivial.
 eqobs_hd iEE_I.
 unfold I; eqobsrel_tail; unfold andR; intros k m1 m2 H;
  decompose [and] H; clear H; split; [ | expr_simpl; repeat split ].
 intros t v Hv; simpl; Vset_mem_inversion Hv; 
  subst; mem_upd_simpl; expr_simpl.
 rewrite (H2 _ Out'), (H0 _ c), (H0 _ Y); auto with set.
 rewrite (H0 _ t), (H2 _ c); auto with set.
 auto with list_op.
 auto with list_op.
 apply (list_ApEq_skipn_compat _ H1 H5).

 (* 3rd subgoal *)
 apply eequiv_cons_equiv with ((Pre L) /-\ (I /-\ (fun k (m1 m2:Mem.t k) => 
  skipn (Lsize k) (m1 In') = skipn (Lsize k) (m2 In')))); trivial.
 eapply equiv_strengthen; [ | apply equiv_assign ].
 intros k m1 m2 (H1,H2); split; [ | split ].
 unfold I, req_mem_rel, andR  in *; decompose [and] H1; 
  clear H1; repeat split; mem_upd_simpl; expr_simpl.
 auto with list_op.

 apply (list_ApEq_first_compat nZeq_bool_spec); trivial.
 apply DiffBound_firstn_compat; trivial.
 refine (dep_I _ _ _ _ _ _ _  H1);
  (apply req_mem_upd_notin_r; [ auto with set | discriminate ]).
 unfold I, req_mem_rel, andR  in *; decompose [and] H1; clear H1.
 expr_simpl; apply (list_ApEq_firstn_neq nZeq_bool_spec H3 H5 H2).
 match goal with 
  |- eequiv (_ /-\ ?P) _ ?C _ _ _ _ _ => 
   rewrite <-(firstn_skipn 2 C);
   apply eequiv_seq_equiv with (req_mem_rel {{Y,t}} P);
    simpl firstn; simpl skipn; trivial
 end.
 eapply eequiv_inv_Modify with (M1:={{t,Y}}) (M2:={{t,Y}})
  (X1:=Vset.union (Vset.union {{Out', c}} {{In'}}) {{In'}})
  (X2:=Vset.union (Vset.union {{Out', c}} {{In'}}) {{In'}}); trivial.
 
 trivial.
 apply (depend_only_andR dep_I);intros k m1 m2 m1' m2' H1 H2 H; 
 rewrite <-(H1 _ In'), <-(H2 _ In'); auto with set.
 apply modify_correct with (refl1_info iEE_I) Vset.empty; apply eq_refl.
 apply modify_correct with (refl1_info iEE_I) Vset.empty; apply eq_refl.
 set (f':=fun k => exp (Eps k * INR (delta k))).
 apply eequiv_weaken with (Pre L /-\ Pre L) (req_mem_rel {{t}} (kreq_mem {{Y}})) 
  (fun k => (f' k * f' k)%R)
  (fun k => max (fzero _ k + f' k ** fzero _ k)%U (fzero _ k + f' k ** fzero _ k)%U); trivial.
 intros k m1 m2 H; split; trivial.
 intros k m1 m2 (H1,H2) t v Hv; Vset_mem_inversion Hv; subst;
  [ apply H2 |  apply H1 ]; auto with set.
 unfold f'; intros n; rewrite <-exp_plus; 
  apply exp_monotonic; rewrite Rmult_assoc; fourier.
 intro k; unfold fzero; multRU_simpl; Usimpl; auto.
 change ([Y <c- PPS2 with {L}; t <c- PrivSum with {L} ]) with
  ([Y <c- PPS2 with {L} ] ++ [ t <c- PrivSum with {L} ]).
 apply eequiv_seq with (req_mem_rel {{Y}} (Pre L)); 
  [ unfold f'; auto | | ].
 apply eequiv_inv_Modify with (M1:={{Y}}) (M2:={{Y}})
  (X1:={{L}}) (X2:={{L}}); trivial.
 unfold f'; auto.
 apply dep_Pre. 
 apply modify_correct with (refl1_info iEE_I) Vset.empty; apply eq_refl.
 apply modify_correct with (refl1_info iEE_I) Vset.empty; apply eq_refl.
 eapply eequiv_weaken; [ | | | | apply PPS2_diff_private ]; 
  auto using (proj2 (req_mem_rel_trueR {{Y}})).
 eapply eequiv_weaken with ((Pre L) /-\ (kreq_mem {{Y}}))
  (req_mem_rel {{t}} (kreq_mem {{Y}})) f' (fzero nat); 
  trivial; try apply (proj1 (andR_comm _ _)).
 apply eequiv_inv_Modify with (M1:={{t}}) (M2:={{t}})
  (X1:={{Y}}) (X2:={{Y}}); trivial.
 unfold f'; auto.
 apply modify_correct with (refl1_info iEE_I) Vset.empty; apply eq_refl.
 apply modify_correct with (refl1_info iEE_I) Vset.empty; apply eq_refl.
 eapply eequiv_weaken; [ | | | | apply PrivSum_diff_private ]; 
  auto using (proj2 (req_mem_rel_trueR {{t}})).
 apply equiv_strengthen with 
  (req_mem_rel (Vset.union {{Y,t}} {{Out',c}}) I').
 unfold I, I', req_mem_rel, andR; intros k m1 m2 H;
  decompose [and] H; clear H; repeat split; trivial.
 apply req_mem_union; trivial.
 eqobs_hd iEE_I'.
 eapply equiv_strengthen; [ | apply equiv_assign ].
 unfold upd_para, I', I, req_mem_rel, andR; intros k m1 m2 H; 
  decompose [and] H; clear H; split; [ expr_simpl; repeat split | ].
 apply req_mem_upd_notin; try discriminate.
 apply req_mem_weaken with (2:=H0); apply eq_refl.
 rewrite H5; trivial.
 auto with list_op.
 rewrite H5; apply (list_ApEq_eq nZeq_bool_spec (eq_refl _)).
 intros t v Hv; Vset_mem_inversion Hv; subst; mem_upd_simpl.

 (* 4th subgoal *)
 apply equiv_eequiv.
 rewrite andR_comm; fold (req_mem_rel {{In'}} I).
 eqobs_hd iEE_I.
 unfold I; eqobsrel_tail; unfold andR; intros k m1 m2 H;
  decompose [and] H; clear H; split; [ | expr_simpl; repeat split ].
 intros t v Hv; simpl; Vset_mem_inversion Hv; 
  subst; mem_upd_simpl; expr_simpl.
 rewrite (H2 _ Out'), (H2 _ c), (H0 _ Y); auto with set.
 rewrite (H2 _ c), (H0 _ t); auto with set.
 auto with list_op.
 auto with list_op.
 apply (list_ApEq_skipn_compat _ H1 H5).
Qed.
