Require Import Extension.
Require Import List.


Open Scope positive_scope.

Notation i := (Var.Lvar T.Nat 1).
Notation G := (Var.Lvar (T.User Graph) 2).
Notation v := (Var.Lvar (T.User Vertex) 3).
Notation L := (Var.Lvar (T.List (T.User Vertex)) 4).

Close Scope positive_scope.


Parameter n : nat.
Hypothesis n_pos : (0 < n)%nat.

Parameter E : env.

Definition c :=
 [ i <- O; L <- Nil _ ] ++
 [
   while (i <! n) do
   [
     v <$- choose G i n;
     L <- v |::| L; 
     G <- G \ v;   
     i <- i +! 1%nat
   ]
 ].

Definition One_extra_edge G1 G2 u v :=
 (forall x y, Gr.in_graph_edge G1 x y -> Gr.in_graph_edge G2 x y) /\
 Gr.in_graph_edge G2 u v /\
 (forall x y, Gr.in_graph_edge G2 x y -> 
   Gr.in_graph_edge G1 x y \/ (x = u /\ y = v) \/ (x = v /\ y = u)).

Definition Pre k (m1 m2:Mem.t k) :=
 (forall x, Gr.in_graph (m1 G) x = Gr.in_graph (m2 G) x) /\
 Gr.size (m1 G) = n /\ 
 (One_extra_edge (m1 G) (m2 G) t_ u_ \/ One_extra_edge  (m2 G) (m1 G) t_ u_).

Definition Post := kreq_mem {{L}}. 

Close Scope bool_scope.

Definition P1 : E.expr T.Bool := (t is_in L) || (u is_in L).
Definition P2 : E.expr T.Bool := (t is_in L) || (u is_in L).


Let loop_body := [ v <$- choose G i n; L <- v |::| L; 
     G <- G \ v; i <- i +! 1%nat ].

Lemma stability: forall k (m:Mem.t k),
  EP k P1 m ->
  range (fun m':Mem.t k => EP k P1 m')
  ([[ loop_body ]] E m).
Proof.
 unfold P1; intros k m H f Hf.
 match goal with 
  |- _ == fmonot (mu ?d ) _ => rewrite <- (mu_zero d)
 end.
 symmetry.
 apply equiv_deno with 
  (P:=req_mem_rel {{i, G, L}} (EP1 P1))
  (Q:=req_mem_rel Vset.empty (EP1 P1)).
 apply equiv_cons with (Q:=req_mem_rel (Vset.singleton v) (EP1 P1)).
 eapply equiv_sub; 
  [ | | apply equiv_random with (Q:=req_mem_rel (Vset.singleton v) (EP1 P1))].
 unfold eq_support, andR, P1, req_mem_rel, kreq_mem, andR, EP, EP1;
  expr_simpl.
 intros ? ? ? [? ?].
 split.
 rewrite (H0 _ i), (H0 _ G); trivial.
 unfold forall_random; intros; expr_simpl; mem_upd_simpl.
 repeat split; trivial.
 intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl.
 trivial.
 eqobsrel_tail; unfold implMR, req_mem_rel, andR;
  simpl; unfold O.eval_op; simpl; repeat split; intuition; mem_upd_simpl.
 unfold EP1, P1 in H2; simpl in H2; unfold O.eval_op in H2; simpl in H2.
 apply orb_prop in H2; destruct H2; rewrite H0.
 rewrite orb_true_r; simpl; trivial.
 rewrite orb_true_r, orb_true_r; simpl; trivial.
 intros; symmetry; apply Hf; destruct H0; trivial.
 split; trivial.
Qed.

Lemma loop_sem: forall k (m:Mem.t k) f,
  mu ([[ [ while i <! n do loop_body ] ]] E m) f ==
  mu (drestr ([[ unroll_while (i <! n) loop_body n]] E m) (negP (EP k (i <! n)))) f.
Proof.
  intros.
  apply deno_bounded_while_elim with (n -! i).
    intros k' m' H' g Hg.
    rewrite <-(firstn_skipn 3%nat loop_body).
    rewrite deno_app_elim, (@Modify_deno_elim E {{G,L,v}} (firstn 3 loop_body));
      [ | apply modify_correct with (refl1_info (empty_info E E)) 
        Vset.empty; apply eq_refl ].
    match goal with |- _ == fmonot (mu ?d) _ => rewrite <-(mu_zero d) end.
    apply mu_stable_eq; unfold fzero; refine (ford_eq_intro _); 
      intro m''; simpl skipn.
    rewrite deno_assign_elim; apply Hg.
    generalize H'; clear; unfold EP; expr_simpl; intro H'.
    apply leb_correct; apply leb_complete in H'; omega.
    intro m'; expr_simpl; intro H'; apply leb_correct_conv; omega.
    expr_simpl; omega.
Qed.



(*  We bound [ Pr [c(G1)=L] / Pr [c(G2)=L] ] when G2 = G1 + {(t,u)}  *)

Definition Pre1 k (m1 m2:Mem.t k) :=
 (Gr.size (m1 G) = Gr.size (m2 G)) /\
 (forall x, Gr.in_graph (m1 G) x = Gr.in_graph (m2 G) x) /\
 (forall x y, Gr.in_graph_edge (m1 G) x y -> Gr.in_graph_edge (m2 G) x y) /\
 Gr.size (m1 G) = n /\ 
 Gr.in_graph_edge (m2 G) t_ u_ /\
 (forall x y, Gr.in_graph_edge (m2 G) x y -> 
   Gr.in_graph_edge (m1 G) x y \/ (x = t_ /\ y = u_) \/ (x = u_ /\ y = t_)).

Definition I : mem_rel :=
 req_mem_rel {{i, L}}
 ((fun k m1 m2 => 
   (forall x, Gr.in_graph (m1 G) x = Gr.in_graph (m2 G) x) /\
   forall x y, Gr.in_graph_edge (m1 G) x y -> Gr.in_graph_edge (m2 G) x y) /-\
  (fun k m1 m2 => 
   if EP k P1 m1 then m1 G = m2 G
   else 
    Gr.in_graph_edge (m2 G) t_ u_ /\
    forall x y, Gr.in_graph_edge (m2 G) x y ->
     Gr.in_graph_edge (m1 G) x y \/ (x = t_ /\ y = u_) \/ (x = u_ /\ y = t_)) /-\
  EP1 (|G| =?= n -! i)).

Hypothesis I_dec : decMR I.

Definition w j : R := ((4 / eps) * sqrt (INR n / INR (n - j)))%R.
Definition lam1 j := exp (if lt_dec j n then 2 / (INR (n - j) * w j) else 0%R).
Definition lam2 := 1%R.
Definition lam (k:nat) := (ProdRR lam1 0 n * lam2)%R.

Lemma lam1_ge_1 : forall j, (1 <= lam1 j)%R.
Proof.
 intros; unfold lam1.
 destruct (lt_dec j n); [ | rewrite exp_0; trivial]. 
 rewrite <-exp_0 at 1.
 apply exp_monotonic.
 apply Rdiv_pos; [fourier | ].
 assert (W:=@US.w_pos j (S n)).
 apply Rmult_lt_0_compat.
 apply lt_0_INR.
 omega.
 apply US.w_pos; trivial.
Qed.

Lemma lam_ge_1 : forall k, (k < n)%nat -> (1 <= lam k)%R.
Proof.
 intros; unfold lam.
 rewrite <-Rmult_1_l at 1; apply Rmult_le_compat;
  [fourier | fourier | | apply Rle_refl]. 
 apply ProdRR_ge_1; intros; apply lam1_ge_1; omega.
Qed.

Hint Resolve lam1_ge_1 lam_ge_1 n_pos I_dec.

Lemma diff_private:
 eequiva Pre1 E c E c Post (fun _ => lam 0) (fun _ => 0).
Proof.
 intros; unfold c.
 set (P:=Pre1 /-\ EP1 (n =?= |G|) /-\ EP1 (i =?= O) /-\ EP1 (L =?= Nil _)).
 eapply eequiva_weaken; [ | | | | eapply eequiva_seq with 
   (lam :=fun _ => 1%R) (lam':=fun _ => lam O) 
   (ep  :=fun _ => 0) (ep' :=fun _ => 0)
   (P:=req_mem_rel Vset.empty Pre1) (Q:=Post) 
   (Q':=req_mem_rel {{i,L}} P)]; trivial.
   unfold req_mem_rel, andR; split; [apply req_mem_empty | trivial].
   intros; simpl; rewrite Rmult_1_l; trivial. 
   intros k; rewrite multRU_0_r, Uplus_zero_left; trivial.
   auto.
 (* Initialization *)
 apply equiv_eequiva.
 eqobsrel_tail; unfold implMR, req_mem_rel, P, Pre1, EP1, andR; simpl; intros;
  decompose [and] H; clear H; repeat split; mem_upd_simpl. 
 unfold O.eval_op; simpl; rewrite H4; apply nat_eqb_refl.

 (* While loop *)
 assert (HI1:implMR I (EP_eq_expr (i <! n) (i <! n))).
   unfold implMR, I, req_mem_rel, andR; intuition.
   unfold EP_eq_expr; simpl; unfold O.eval_op; simpl; rewrite H0; trivial.
 assert (HI2:implMR I (EP_eq_expr P1 P2)).
   unfold implMR, I, req_mem_rel, andR; intros; intuition.
   unfold EP_eq_expr; simpl; unfold O.eval_op; simpl; rewrite H0; trivial.

 eapply eequiva_weaken with (lam':=fun _ => lam 0) (ep' :=fun _ => 0)
  (P':=I /-\ EP1 (i =?= O) /-\ EP1 (!P1)) (Q':=I /-\ EP1 (!i <! n));
  [ | | | | apply eequiva_while_split with (P2:=P2)
    (lam1:=lam1) (lam2:=lam2) (n:=n)]; trivial.

 unfold implMR, I, P, Pre1, req_mem_rel, andR, P1.
 intros k m1 m2 H; decompose [and] H; clear H.
 generalize H3, H7, H10; clear H3 H7 H10; expr_simpl; intros.
 apply nat_eqb_true in H3; apply nat_eqb_true in H7.
 generalize (eqb_list_spec Gr.v_eqb Gr.v_eqb_spec (m1 L) (@nil Gr.vertex)).
 rewrite H10; clear H10; intro.
 repeat split; trivial.
 unfold EP; expr_simpl.
 rewrite H; simpl; split; trivial.
 rewrite H7, H3, <-minus_n_O; apply nat_eqb_refl.
 rewrite H3; apply nat_eqb_refl.
 rewrite H; trivial.
 unfold implMR, I, Post, req_mem_rel, andR, P1; intuition.
 apply req_mem_weaken with (2:=H); vm_compute; trivial.
 6:intros; auto.
 Focus 6.
 intros; unfold lam; apply Rmult_le_compat; [ | | | trivial].
 rewrite <-ProdRR_ge_1; [fourier | trivial].
 unfold lam2; fourier.
 apply ProdRR_ge_1_monotonic; trivial.

 (* 1st proof obligation of while rule *)
 intro j.
 set (P':=(t is_in (v |::| L)) || (u is_in (v |::| L))).
 apply eequiva_eq_compat_l with 
  ([ v <$- choose G i n; Assert !P' ] ++
   [ L <- v |::| L; G <- G \ v; i <- i +! 1%nat]).
   intros; simpl app. 
   repeat elim_random.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m''.
   repeat (elim_assign || elim_assert).
   match goal with 
    |- (match ?C1' with |true => _ |false => _ end) == 
       (match ?C2' with |true => _ |false => _ end) => 
       assert (C1' = C2') by (expr_simpl; apply f_equal;
         rewrite <- H0; simpl; mem_upd_simpl)
   end.
   rewrite <- H0.
   case_eq (E.eval_expr (!P') (m1{!v <-- m''!})); intro HP; simpl O.tres in HP;
    rewrite HP; trivial.
   repeat elim_assign; rewrite deno_nil_elim.
   mem_upd_simpl; trivial.

 apply eequiva_eq_compat_r with 
  ([ v <$- choose G i n; Assert !P' ] ++
   [ L <- v |::| L; G <- G \ v; i <- i +! 1%nat]).
   intros; simpl app. 
   repeat elim_random.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m''.
   repeat (elim_assign || elim_assert).
   match goal with 
    |- (match ?C1' with |true => _ |false => _ end) == 
       (match ?C2' with |true => _ |false => _ end) => 
       assert (C1' = C2') by (expr_simpl; apply f_equal; 
         rewrite <- H0; simpl; mem_upd_simpl)
   end.
   rewrite <- H0.
   case_eq (E.eval_expr (!P') (m2{!v <-- m''!})); intro HP; simpl O.tres in HP; 
    rewrite HP; trivial.
   repeat elim_assign; rewrite deno_nil_elim.
   mem_upd_simpl; trivial.

 eapply eequiva_weaken with (lam':=fun _ => (lam1 j * 1)%R) (ep' :=fun _ => 0 + _ ** 0)
  (Q':=req_mem_rel Vset.empty (I /-\ EP1 (i =?= S j) /-\ EP1 (!P1)));
  [ | | | | apply eequiva_seq with (Q':=req_mem_rel {{v}} 
     (EP1 (v \in G) /-\ I /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (!P'))) ].
   trivial.
   unfold implMR, I, req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H.
   generalize H5, H7, H8; clear H5 H7 H8; expr_simpl; intros.
   apply nat_eqb_true in H5; apply nat_eqb_true in H7.
   rewrite negb_orb in H8; apply andb_prop in H8; destruct H8 as [H9 H10].
   repeat split; trivial.
   rewrite H7, H5; apply nat_eqb_refl.
   rewrite H5; apply nat_eqb_refl.
   rewrite negb_orb, H9, H10; trivial.
   intros; rewrite Rmult_1_r; trivial.
   intros ?; rewrite multRU_0_r, Uplus_zero_left; trivial.
   trivial.

 apply eequiva_weaken with (lam':=fun _ => lam1 j) (ep' := fun _ => 0)
   (P':=(I /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (!P1)) /-\ 
       (I /-\ EP1 (i <! n) /-\ EP1 (i =?= j)))
   (Q':=((req_mem_rel {{v}} (EP1 (!P')) /-\ EP1 (v \in G)) /-\ 
   (I /-\ EP1 (i <! n) /-\ EP1 (i =?= j)))); trivial.
   unfold implMR, I, req_mem_rel, andR; intuition.
   unfold implMR, req_mem_rel, andR; intuition.
 apply eequiva_inv_Modify with {{i,G,L}} {{i,G,L}} {{v}} {{v}}; trivial.
   unfold depend_only_rel, I, req_mem_rel, andR, EP1; intuition. 
   apply req_mem_trans with m1.
     apply req_mem_sym; apply req_mem_weaken with (2:=H).
     vm_compute; trivial.
     apply req_mem_trans with m2; trivial.
     apply req_mem_weaken with (2:=H0); apply eq_refl.
   rewrite <-(H _ G), <-(H0 _ G); trivial.
   generalize H6; rewrite <-(H _ G), <-(H0 _ G); auto.
   unfold EP, P1; expr_simpl; rewrite <-(H _ G), <-(H0 _ G), <-(H _ L); trivial.
   expr_simpl; rewrite <-(H _ i); trivial.
   generalize H8; expr_simpl; rewrite <-(H _ G); trivial.
   expr_simpl; rewrite <-(H _ i); trivial.
   expr_simpl; rewrite <-(H _ i); trivial.
   apply modify_correct with (refl1_info (empty_info E E)) Vset.empty; apply eq_refl.
   apply modify_correct with (refl1_info (empty_info E E)) Vset.empty; apply eq_refl.
 
 apply eequiva_range_l.
   intros k m1 m2 [ [_ [_ [_ ?] ] ] [? _] ] f Hf.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   simpl DE.eval_support.
   apply US.weighted_choice_in_graph.
     unfold EP1 in H0; simpl in H0; unfold O.eval_op in H0; simpl in H0.
     rewrite plus_comm in H0; apply leb_complete; trivial.
     apply nat_eqb_true; trivial.
     intros; rewrite deno_assert_elim.
     case (@E.eval_expr _ T.Bool (!P') (m1{!v <-- x!}));
       [ apply Hf; expr_simpl | trivial ].

 (* Random sampling *)
 apply eequiva_weaken with (lam':=fun _ => lam1 j) (ep' :=fun _ => 0)
  (P':=I /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (!P1))
  (Q':=EP_eq_expr v v /-\ EP1 (!P') /-\ EP2 (!P'));
  [ | | | |  apply eequiva_random_assert_strong ]; trivial.
  unfold implMR, req_mem_rel, andR, EP_eq_expr; intuition.
  intros ? ? Hin; Vset_mem_inversion Hin; subst; trivial.
  
 unfold I, req_mem_rel, andR; intros; decompose [and] H; clear H.
 unfold EP1 in H8; unfold EP in H0; rewrite eval_negb in H8;
   apply is_true_negb in H8; apply not_is_true_false in H8. 
 rewrite H8 in H0; destruct H0.
 unfold P1 in H8; simpl in H8; unfold O.eval_op in H8; simpl in H8;
   apply orb_false_elim in H8; destruct H8.
 match goal with |- le_dist_asym ?D1' ?D2' _ _ => 
   assert (HdL: is_Discrete D1'); [ | assert (HdR: is_Discrete D2') ] 
 end.
   apply (is_Discrete_Mlet _ (DE.discrete_support _ _)).
   intros a; case (@E.eval_expr _ T.Bool (!P') (m1 {!v <-- a!}));
    [ apply is_Discrete_Munit | apply 
      (is_Discrete_distr0  (T.default k (T.User Vertex))) ].
   apply (is_Discrete_Mlet _ (DE.discrete_support _ _)).
   intros a; case (@E.eval_expr _ T.Bool (!P') (m2 {!v <-- a!}));
    [ apply is_Discrete_Munit | apply 
      (is_Discrete_distr0  (T.default k (T.User Vertex))) ].
 eapply le_dist_asym_weaken_ep; [ |
  eapply le_dist_asym_discr_pointwise_ub with (F:=fun _ => 0) ].
   rewrite serie_zero; auto.
   apply carT_cover.
   apply lam1_ge_1.
   apply (disc_eqpoint_r HdR HdL).
   apply (disc_eqpoint_l HdR HdL).
  
 intro; simpl; expr_simpl.
 rewrite (H2 _ i); [ | trivial].

 Open Scope bool_scope.

 transitivity 
  (mu (US.weighted_choice (m1 G) (m2 i) n)
    (fun x => 
     if (negb (Gr.v_eqb u_ a || Gr.v_eqb t_ a) && Gr.v_eqb a x) then 1 else 0) -
   lam1 j **
   (mu (US.weighted_choice (m2 G) (m2 i) n)
     (fun x =>
      if (negb (Gr.v_eqb u_ a || Gr.v_eqb t_ a) && Gr.v_eqb a x) then 1 else 0))).
   apply Uminus_le_compat.
     refine (mu_monotonic _ _ _ _); intro; mem_upd_simpl.
     rewrite H7, H8, orb_false_r, orb_false_r; trivial.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     rewrite andb_true_r; unfold carT; simpl.
     case (negb (Gr.v_eqb u_ x || Gr.v_eqb t_ x)); trivial.
     rewrite andb_false_r; unfold carT; simpl.
     case (negb (Gr.v_eqb u_ x || Gr.v_eqb t_ x)); trivial.
     simpl.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     tauto.
     trivial.
     apply multRU_le_compat.
     rewrite <-lam1_ge_1; fourier.
     trivial.
     refine (mu_monotonic _ _ _ _); intro; mem_upd_simpl.
     rewrite <-(H2 _ L), H7, H8, orb_false_r, orb_false_r; trivial.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     rewrite andb_true_r; unfold carT; simpl.
     case (negb (Gr.v_eqb u_ x || Gr.v_eqb t_ x)); trivial.
     simpl; rewrite Gr_v_eqb_refl; trivial.
     rewrite andb_false_r; unfold carT; simpl.
     trivial.
 
 apply Uminus_le_zero.
 case_eq (negb (Gr.v_eqb u_ a || Gr.v_eqb t_ a)); intro Heq; simpl.
 case_eq (Gr.in_graph (m1 G) a); intro Ha.

 rewrite negb_orb in Heq; apply andb_prop in Heq.
 generalize H1, H4; clear H1 H4; unfold EP1; expr_simpl; intros.
 apply leb_complete in H4; apply nat_eqb_true in H1.
 rewrite <-H2; trivial; rewrite H1 in *.
 rewrite <-retract_U.
 fold (US.carV a); rewrite US.weighted_choice_spec_in.
 rewrite <-(retract_U (mu (US.weighted_choice (m2 G) j n) (US.carV a))).
 rewrite US.weighted_choice_spec_in.
 rewrite <-(retract_U 
  (lam1 j **
   iU
   ((INR (Gr.degree (m2 G) a) + US.w j n) /
    (INR (Gr.weight (m2 G)) + INR (n - j) * US.w j n)))).
 apply iU_le.
 destruct (Rle_dec
  (lam1 j *
   iR (iU
    ((INR (Gr.degree (m2 G) a) + US.w j n) /
     (INR (Gr.weight (m2 G)) + INR (n - j) * US.w j n)))) 1%R). 
 rewrite multRU_Rmult_b, retract_R; trivial.

 generalize (Gr.eqb_spec (m1 G) (m2 G)); case (Gr.eqb (m1 G) (m2 G)); intro HG.
 rewrite HG.
 rewrite <-Rmult_1_l at 1; apply Rmult_le_compat.
 fourier.
 apply Rdiv_pos.
 apply Rplus_le_le_0_compat.
 apply pos_INR.
 apply Rlt_le, US.w_pos; omega.
 apply Rplus_le_lt_0_compat.
 apply pos_INR.
 apply Rmult_lt_0_compat.
 apply lt_0_INR; omega.
 apply US.w_pos; omega.
 apply lam1_ge_1.
 trivial.

 rewrite <-Gr.weight_diff with (G1:=m1 G) (G2:=m2 G) (t_:=t_) (u_:=u_); trivial.
 assert ((INR (Gr.degree (m1 G) a) + US.w j n) /
  (INR (Gr.weight (m1 G)) + INR (n - j) * US.w j n) =
  (INR (Gr.degree (m1 G) a) + US.w j n) * 1 /
  (INR (Gr.weight (m1 G)) + INR (n - j) * US.w j n))%R. 
 field.
 apply not_eq_sym, Rlt_not_eq.
 rewrite <-Rplus_0_l at 1.
 apply Rplus_le_lt_compat.
 auto.
 apply Rmult_lt_0_compat.
 apply lt_0_INR; omega.
 apply US.w_pos; omega.

 rewrite H9.
 assert (lam1 j *
  ((INR (Gr.degree (m2 G) a) + US.w j n) /
   (INR (Gr.weight (m1 G) + 2) + INR (n - j) * US.w j n)) =
  (INR (Gr.degree (m2 G) a) + US.w j n) * 
  (lam1 j  / 
   (INR (Gr.weight (m1 G) + 2%nat) + INR (n - j) * US.w j n)))%R.
 field.
 apply not_eq_sym, Rlt_not_eq.
 rewrite <-Rplus_0_l at 1.
 apply Rplus_le_lt_compat.
 auto.
 apply Rmult_lt_0_compat.
 apply lt_0_INR; omega.
 apply US.w_pos; omega.

 rewrite H10.
 apply Rmult_le_compat.
 rewrite Rmult_1_r.
 apply Rplus_le_le_0_compat; [apply pos_INR | apply Rlt_le; apply US.w_pos].
 omega.

 rewrite <-(Rmult_1_l ( / (INR (Gr.weight (m1 G)) + INR (n - j) * US.w j n))%R).
 apply Rle_mult_inv_pos; [fourier | ].
 apply Rplus_le_lt_0_compat; [ apply pos_INR | ].
 apply Rmult_lt_0_compat; [ | apply US.w_pos].
 apply lt_0_INR; omega.
 omega.
 
 rewrite Rmult_1_r.
 assert (Gr.degree (m1 G) a = Gr.degree (m2 G) a).
 destruct Heq as [X1 X2]; apply negb_true_iff in X1; apply negb_true_iff in X2.
 apply Gr.degree_diff_neq with t_ u_; auto.
 generalize (Gr.v_eqb_spec t_ a); destruct (Gr.v_eqb t_ a);
  [discriminate | apply not_eq_sym; trivial].
 generalize (Gr.v_eqb_spec u_ a); destruct (Gr.v_eqb u_ a);
  [discriminate | apply not_eq_sym; trivial].

 rewrite H11; trivial.
 assert (W:(INR (Gr.weight (m1 G) + 2) + INR (n - j) * US.w j n <=
  lam1 j * (INR (Gr.weight (m1 G)) + INR (n - j) * US.w j n))%R).
 rewrite (Rmult_comm (lam1 j)), Rmult_plus_distr_r.
 rewrite plus_INR.
 rewrite (Rplus_assoc (INR (Gr.weight (m1 G)))).
 apply Rplus_le_compat.
 rewrite <-Rmult_1_r at 1; apply Rmult_le_compat.
 auto.
 fourier.
 trivial.
 apply lam1_ge_1.

 unfold lam1.
 destruct (lt_dec j n); [ | exfalso; omega].
 unfold US.w, w.
 set (U:=(INR (n - j) * (4 / eps * sqrt (INR n / INR (n - j))))%R).
 assert (U_pos: (0 < U)%R).
 apply Rmult_lt_0_compat.
 apply lt_0_INR; omega.
 apply Rmult_lt_0_compat.
 apply Rdiv_lt_0.
 fourier.
 apply eps_pos.
 apply sqrt_lt_R0.
 apply Rdiv_lt_0.
 apply lt_0_INR, n_pos.
 apply lt_0_INR; omega.
 
 transitivity (U * (1 + 2 / U))%R.
 rewrite Rmult_plus_distr_l, Rmult_1_r, Rplus_comm.
 apply Rplus_le_compat; [trivial | ].
 simpl INR; apply Req_le; field.
 apply not_eq_sym, Rlt_not_eq; trivial.

 apply Rmult_le_compat.
 fourier.
 apply Rle_zero_pos_plus1.
 apply Rdiv_pos; fourier.
 trivial.
 apply Rlt_le, exp_ineq1.
 apply Rdiv_lt_0; fourier.

 set (X:=(INR (Gr.weight (m1 G)) + INR (n - j) * US.w j n)%R).
 set (Y:=(INR (Gr.weight (m1 G) + 2) + INR (n - j) * US.w j n)%R).
 assert (0 < X)%R.
 apply Rplus_le_lt_0_compat.
 auto.
 apply Rmult_lt_0_compat.
 apply lt_0_INR; omega.
 apply US.w_pos; omega.

 assert (0 < Y)%R.
 apply Rplus_le_lt_0_compat.
 auto.
 apply Rmult_lt_0_compat.
 apply lt_0_INR; omega.
 apply US.w_pos; omega.
 
 apply Rmult_le_reg_l with Y; trivial.
 apply Rmult_le_reg_r with X; trivial.
 replace (Y * / X * X)%R with Y.
 replace (Y * (lam1 j / Y) * X)%R with (lam1 j * X)%R.
 trivial.
 field; apply not_eq_sym, Rlt_not_eq; trivial.
 field; apply not_eq_sym, Rlt_not_eq; trivial.


 rewrite <-US.weighted_choice_spec_in; trivial.
 apply iR_bound.
 omega.
 rewrite <-H3; trivial.
 apply nat_eqb_true; rewrite <-H1.
 rewrite <-(Gr.size_eq H3); trivial.

 transitivity 1%R.
 apply Rmult_le_reg_r with 
  (INR (Gr.weight (m1 G)) + INR (n - j) * US.w j n)%R.
 apply Rplus_le_lt_0_compat.
 auto.
 apply Rmult_lt_0_compat.
 apply lt_0_INR; omega.
 apply US.w_pos; omega.

 rewrite Rdiv_mult, Rmult_1_l.
 apply Rplus_le_compat.
 apply le_INR.
 eapply le_trans; [ | apply (Gr.degree_le_weight _ a)]; omega.
 rewrite <-Rmult_1_l at 1.
 apply Rmult_le_compat.
 fourier.
 apply Rlt_le, US.w_pos; omega.
 change 1%R with (INR 1)%R.
 apply le_INR; omega.
 trivial.

 apply Rplus_le_lt_0_compat.
 auto.
 apply Rmult_lt_0_compat.
 apply lt_0_INR; omega.
 apply US.w_pos; omega.

 apply Rnot_le_lt in n0.
 unfold multRU.
 match goal with
  |- context [Rle_dec ?x ?y] => destruct (Rle_dec x y)
 end.
 contradict r; apply Rlt_not_le; trivial.
 rewrite iR_1; trivial.
 omega.
 rewrite <-H3; trivial.
 apply nat_eqb_true; rewrite <-H1.
 rewrite <-(Gr.size_eq H3); trivial.
 omega.
 trivial.
 apply nat_eqb_true; rewrite <-H1; trivial.

 (* a \notin G1 *)
 fold (US.carV a).
 rewrite US.weighted_choice_spec_notin.
 auto.
 rewrite <-H2; [ | trivial].
 apply leb_complete; change (S (m1 i)) with (1 + m1 i)%nat; 
  rewrite plus_comm; trivial.
 rewrite <-H2; [ | trivial]; apply nat_eqb_true; trivial.
 trivialb.

 rewrite (@mu_zero Gr.vertex); trivial.

 unfold I, req_mem_rel, kreq_mem, andR; intros; decompose [and] H.
 unfold P'; expr_simpl.
 rewrite (H2 _ L).
 trivial.
 vm_compute; trivial.

 (* Continuing... *)
 
 Opaque Vset.add.

 apply equiv_eequiva.
 eqobsrel_tail; unfold implMR, I, req_mem_rel, andR;
  simpl; unfold O.eval_op; simpl; repeat split; intuition; mem_upd_simpl.
   rewrite (H0 _ v), (H2 _ L), (H2 _ i); trivial.
   intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl. 
   rewrite (H0 _ v); trivial.
   unfold EP1, P' in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
   apply Gr.in_graph_remove_vertex; auto.
   generalize H6; mem_upd_simpl; clear H6; intro.
   rewrite <-(H0 _ v); [ | trivial].
   generalize (Gr.v_eqb_spec (m1 v) x); destruct (Gr.v_eqb (m1 v) x); intro.
   subst.
   apply Gr.edge_vertex in H6; destruct H6.
   contradict H6; apply Gr.remove_vertex_eq.
   generalize (Gr.v_eqb_spec (m1 v) y); destruct (Gr.v_eqb (m1 v) y); intro. 
   subst.
   apply Gr.edge_vertex in H6; destruct H6.
   contradict H11; apply Gr.remove_vertex_eq.
   apply Gr.in_graph_remove_edge_neq; trivial.
   apply H8.
   apply Gr.in_graph_remove_edge_conv in H6; trivial.

   unfold EP, P1; expr_simpl; mem_upd_simpl.
   unfold EP1, P' in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
   rewrite negb_orb in H7; apply andb_prop in H7; destruct H7.
   rewrite negb_orb in H6, H7; apply andb_prop in H6; apply andb_prop in H7.
   destruct H6; destruct H7.
   simpl; rewrite negb_true_iff in H6, H7, H10, H11; rewrite H6, H7, H10, H11; simpl.
   assert (W:EP k P1 m1 = false) by 
    (unfold EP, P1; expr_simpl; rewrite H10, H11; trivial).
   rewrite W in H3; clear W; destruct H3.
   split.
     apply Gr.in_graph_remove_edge_neq; trivial.
     rewrite <-H0; trivial; intro Heq; rewrite Heq in H7.
     rewrite Gr_v_eqb_refl in H7; discriminate H7.
     rewrite <-H0; trivial; intro Heq; rewrite Heq in H6.
     rewrite Gr_v_eqb_refl in H6; discriminate H6.
     intros.
     generalize (Gr.v_eqb_spec (m2 v) x); destruct (Gr.v_eqb (m2 v) x); intro Hx. 
     subst.
     apply Gr.edge_vertex in H13; destruct H13.
     contradict H13; apply Gr.remove_vertex_eq.
     generalize (Gr.v_eqb_spec (m2 v) y); destruct (Gr.v_eqb (m2 v) y); intro Hy. 
     subst.
     apply Gr.edge_vertex in H13; destruct H13.
     contradict H14; apply Gr.remove_vertex_eq.
     rewrite (H0 _ v); trivial.
     assert (Gr.in_graph_edge (m2 G) x y) by 
       (apply Gr.in_graph_remove_edge_conv in H13; trivial).
     decompose [and or] (H12 _ _ H14); clear H12 H14; trivial; subst.
     left; apply Gr.in_graph_remove_edge_neq; trivial.
     right; auto.
     right; auto.
   generalize H9; unfold EP1; expr_simpl; mem_upd_simpl.
   intro Heq; apply nat_eqb_true in Heq.
   rewrite Gr.remove_vertex_size; [ | trivial].
   rewrite Heq.
   replace (pred (n - m1 i))%nat with (n - (m1 i + 1))%nat by omega.
   apply nat_eqb_refl.
   generalize H4; clear H4; expr_simpl; intro Heq.
   apply nat_eqb_true in Heq; rewrite Heq, plus_comm; apply nat_eqb_refl.

 (* 2nd proof obligation of while rule *)
 Close Scope bool_scope.

 intro j.
 set (P':=(t is_in (v |::| L)) || (u is_in (v |::| L))).
 apply eequiva_eq_compat_l with 
  ([ v <$- choose G i n; Assert P' ] ++
   [ L <- v |::| L; G <- G \ v; i <- i +! 1%nat]).
   intros; simpl app. 
   repeat elim_random.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m''.
   repeat (elim_assign || elim_assert).
   match goal with 
    |- (match ?C1' with |true => _ |false => _ end) == 
       (match ?C2' with |true => _ |false => _ end) => 
       assert (C1' = C2') by (expr_simpl; apply f_equal;
         rewrite <- H0; simpl; mem_upd_simpl)
   end.
   rewrite <- H0.
   case_eq (E.eval_expr (P') (m1{!v <-- m''!})); intro HP; simpl O.tres in HP;
    rewrite HP; trivial.
   repeat elim_assign; rewrite deno_nil_elim.
   mem_upd_simpl; trivial.

 apply eequiva_eq_compat_r with 
  ([ v <$- choose G i n; Assert P' ] ++
   [ L <- v |::| L; G <- G \ v; i <- i +! 1%nat]).
   intros; simpl app. 
   repeat elim_random.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m''.
   repeat (elim_assign || elim_assert).
   match goal with 
    |- (match ?C1' with |true => _ |false => _ end) == 
       (match ?C2' with |true => _ |false => _ end) => 
       assert (C1' = C2') by (expr_simpl; apply f_equal; 
         rewrite <- H0; simpl; mem_upd_simpl)
   end.
   rewrite <- H0.
   case_eq (E.eval_expr (P') (m2{!v <-- m''!})); intro HP; simpl O.tres in HP; 
    rewrite HP; trivial.
   repeat elim_assign; rewrite deno_nil_elim.
   mem_upd_simpl; trivial.

 eapply eequiva_weaken with (lam':=fun _ => (lam2 * 1)%R) (ep' :=fun _ => 0 + _ ** 0)
  (Q':=req_mem_rel Vset.empty (I /-\ EP1 (i =?= S j) /-\ EP1 (P1)));
  [ | | | | apply eequiva_seq with (Q':=req_mem_rel {{v}} 
     (EP1 (v \in G) /-\ I /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (P'))) ].
   trivial.
   unfold implMR, req_mem_rel, andR; intuition.
   intros; rewrite Rmult_1_r; trivial.
   intros ?; rewrite multRU_0_r, Uplus_zero_left; trivial.
   trivial.

 apply eequiva_weaken with (lam':=fun _ => lam2) (ep' := fun _ => 0)
   (P':=(I /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (!P1)) /-\ 
       (I /-\ EP1 (i <! n) /-\ EP1 (i =?= j)))
   (Q':=((req_mem_rel {{v}} (EP1 P') /-\ EP1 (v \in G)) /-\ 
   (I /-\ EP1 (i <! n) /-\ EP1 (i =?= j)))); trivial.
   unfold implMR, I, req_mem_rel, andR; intuition.
   unfold implMR, req_mem_rel, andR; intuition.
 apply eequiva_inv_Modify with {{i,G,L}} {{i,G,L}} {{v}} {{v}}; trivial.
   unfold depend_only_rel, I, req_mem_rel, andR, EP1; intuition. 
   apply req_mem_trans with m1.
     apply req_mem_sym; apply req_mem_weaken with (2:=H).
     vm_compute; trivial.
     apply req_mem_trans with m2; trivial.
     apply req_mem_weaken with (2:=H0); apply eq_refl.
   rewrite <-(H _ G), <-(H0 _ G); trivial.
   generalize H6; rewrite <-(H _ G), <-(H0 _ G); auto.
   unfold EP, P1; expr_simpl; rewrite <-(H _ G), <-(H0 _ G), <-(H _ L); trivial.
   expr_simpl; rewrite <-(H _ i); trivial.
   generalize H8; expr_simpl; rewrite <-(H _ G); trivial.
   expr_simpl; rewrite <-(H _ i); trivial.
   expr_simpl; rewrite <-(H _ i); trivial.
   apply modify_correct with (refl1_info (empty_info E E)) Vset.empty; apply eq_refl.
   apply modify_correct with (refl1_info (empty_info E E)) Vset.empty; apply eq_refl.
 
 apply eequiva_range_l.
   intros k m1 m2 [ [_ [_ [_ ?] ] ] [? _] ] f Hf.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   simpl DE.eval_support.
   apply US.weighted_choice_in_graph.
     apply leb_complete; change (S (m1 i)) with (1 + m1 i)%nat; rewrite plus_comm; 
       trivial.
     apply nat_eqb_true; trivial.
     intros; rewrite deno_assert_elim.
     case (@E.eval_expr _ T.Bool P' (m1{!v <-- x!}));
       [ apply Hf; expr_simpl | trivial ].

 (* Random sampling *)
 apply eequiva_weaken with (lam':=fun _ => lam2) (ep' :=fun _ => 0)
  (P':=I /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (!P1))
  (Q':=EP_eq_expr v v /-\ EP1 P' /-\ EP2 P');
  [ | | | |  apply eequiva_random_assert_strong ]; trivial.
  unfold implMR, req_mem_rel, andR, EP_eq_expr; intuition.
  intros ? ? Hin; Vset_mem_inversion Hin; subst; trivial.
  
 unfold I, req_mem_rel, andR; intros; decompose [and] H;
   clear H; simpl; expr_simpl.
 unfold EP1 in H8; unfold EP in H0; rewrite eval_negb in H8.
 apply is_true_negb in H8; apply not_is_true_false in H8;
   rewrite H8 in H0; destruct H0.
 unfold P1 in H8; simpl in H8; unfold O.eval_op in H8; simpl in H8.
 apply orb_false_elim in H8; destruct H8.
 match goal with |- le_dist_asym ?D1' ?D2' _ _ => 
   assert (HdL: is_Discrete D1'); [ | assert (HdR: is_Discrete D2') ] 
 end.
   apply is_Discrete_Mlet.
   unfold US.weighted_choice.
   destruct (le_lt_dec n (m1 i)); [ apply is_Discrete_Munit | ].
   destruct (Gr_is_empty_dec (m1 G)); [ apply is_Discrete_Munit | ].
   destruct (Gr.not_is_empty (g:=m1 G) n0); apply finite_distr_discrete.
   intro a.
    match goal with |- context [is_Discrete (if ?CC then _ else _)] => 
      destruct CC end.
   apply is_Discrete_Munit.
   apply (is_Discrete_distr0 (T.default k (T.User Vertex))).
   apply is_Discrete_Mlet.
   unfold US.weighted_choice.
   destruct (le_lt_dec n (m2 i)); [ apply is_Discrete_Munit | ].
   destruct (Gr_is_empty_dec (m2 G)); [ apply is_Discrete_Munit | ].
   destruct (Gr.not_is_empty (g:=m2 G) n0); apply finite_distr_discrete.
   intro a.
    match goal with |- context [is_Discrete (if ?CC then _ else _)] => 
      destruct CC end.
   apply is_Discrete_Munit.
   apply (is_Discrete_distr0 (T.default k (T.User Vertex))).
 eapply le_dist_asym_weaken_ep; [ |
  eapply le_dist_asym_discr_pointwise_ub with (F:=fun _ => 0) ].
   rewrite serie_zero; auto.
   apply US.carV_prop.
   trivial.
   apply (disc_eqpoint_r HdR HdL).
   apply (disc_eqpoint_l HdR HdL).
  
 Open Scope bool_scope.
 intro; simpl; expr_simpl.
 rewrite (H2 _ i); [ | trivial].

 transitivity 
  (mu (US.weighted_choice (m1 G) (m2 i) n)
    (fun x => 
     if ((Gr.v_eqb u_ a || Gr.v_eqb t_ a) && Gr.v_eqb a x) then 1 else 0) -
   lam2 **
   (mu (US.weighted_choice (m2 G) (m2 i) n)
     (fun x =>
      if ((Gr.v_eqb u_ a || Gr.v_eqb t_ a) && Gr.v_eqb a x) then 1 else 0))).
   apply Uminus_le_compat.
     refine (mu_monotonic _ _ _ _); intro; mem_upd_simpl.
     rewrite H7, H8, orb_false_r, orb_false_r; trivial.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     rewrite andb_true_r; unfold carT; simpl.
     case (Gr.v_eqb u_ x || Gr.v_eqb t_ x); trivial.
     rewrite andb_false_r; unfold carT; simpl.
     case (Gr.v_eqb u_ x || Gr.v_eqb t_ x); trivial.
     unfold US.carV; simpl.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     tauto.
     trivial.
     apply multRU_le_compat.
     unfold lam2; fourier.
     trivial.
     refine (mu_monotonic _ _ _ _); intro; mem_upd_simpl.
     rewrite <-(H2 _ L), H7, H8, orb_false_r, orb_false_r; trivial.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     rewrite andb_true_r; unfold  US.carV, carT; simpl.
     case (Gr.v_eqb u_ x || Gr.v_eqb t_ x); trivial.
     simpl; rewrite Gr_v_eqb_refl; trivial.
     rewrite andb_false_r; unfold carT; simpl.
     trivial.
 
 apply Uminus_le_zero.
 case_eq (Gr.v_eqb u_ a || Gr.v_eqb t_ a); intro Heq; simpl.
 case_eq (Gr.in_graph (m1 G) a); intro Ha.

 (* case [a in G1] *)
 apply orb_prop in Heq.
 generalize H4, H1; clear H4 H1; unfold EP1; expr_simpl; intros.
 apply leb_complete in H4; apply nat_eqb_true in H1.
 rewrite <-H2; trivial; rewrite H1 in *.


 unfold lam2; rewrite multRU_1_l.
 rewrite <-retract_U.
 fold (US.carV a); rewrite US.weighted_choice_spec_in.
 rewrite <-(retract_U (mu (US.weighted_choice _ _ _) _)).
 rewrite US.weighted_choice_spec_in.
 apply iU_le.

 generalize (Gr.eqb_spec (m1 G) (m2 G)); case (Gr.eqb (m1 G) (m2 G)); intro HG.

 (* case [m1 G = m2 G] *)
 rewrite HG; trivial.

 (* case [m1 G <> m2 G] *)
 rewrite <-Gr.weight_diff with (G1:=m1 G) (G2:=m2 G) (t_:=t_) (u_:=u_); trivial.
 destruct (Gr.degree_diff_eq (G1:=m1 G) (G2:=m2 G) (t_:=t_) (u_:=u_)); trivial.

 assert (Aux : forall G' s,
   let X := (INR (Gr.degree G' s) + US.w j n)%R in
   let Y := (INR (Gr.weight G') + INR (n - j) * US.w j n)%R in
     (X / Y <= (X + 1) / (Y + 2))%R).
   intros.
   assert (0 < X)%R by (apply Rplus_le_lt_0_compat; [ auto | apply US.w_pos; omega ]).
   assert (0 < Y)%R by (apply Rplus_le_lt_0_compat; [ auto | 
     apply Rmult_lt_0_compat; [ apply lt_0_INR | apply US.w_pos]; omega ]).
   apply Rmult_le_reg_l with Y; trivial.
   apply Rmult_le_reg_r with (Y + 2)%R; trivial.
   fourier.
   replace (Y * (X / Y) * (Y + 2))%R with (X * Y + 2 * X)%R by
     (field; apply not_eq_sym, Rlt_not_eq; trivial).
   replace (Y * ((X + 1) / (Y + 2)) * (Y + 2))%R with (X * Y + Y)%R by
     (field; apply not_eq_sym, Rlt_not_eq; fourier).
   apply Rplus_le_compat; [trivial | ].
   unfold X, Y; rewrite Rmult_plus_distr_l.
   destruct (eq_nat_dec (n - j) 1%nat) as [Hj | Hj].
   elim t_neq_u.
   apply Gr.edge_vertex in H; destruct H as [Ht Hu].
   generalize H6; unfold EP1; expr_simpl; intro Hsize.
   apply nat_eqb_true in Hsize; rewrite H1, Hj in Hsize.
   apply Gr.size_1_inversion with (1:=Hsize); rewrite H3; trivial.
   assert (2 <= INR (n - j))%R by (change 2%R with (INR 2); apply le_INR; omega). 
   apply Rplus_le_compat.
   change 2%R with (INR 2); rewrite <-mult_INR.
   apply le_INR, Gr.degree_le_weight.
   apply Rmult_le_compat; trivial.
   fourier.
   apply Rlt_le, US.w_pos; omega.

 destruct Heq as [Heq | Heq]; apply Gr_v_eqb_true in Heq; subst a.

 (* case [a = u] *)
 rewrite H10.
 rewrite S_INR, Rplus_assoc, (Rplus_comm 1), <-Rplus_assoc. 
 set (X:=(INR (Gr.degree (m1 G) u_) + US.w j n)%R).
 rewrite plus_INR, Rplus_assoc, (Rplus_comm 2), <-Rplus_assoc.
 set (Y:=(INR (Gr.weight (m1 G)) + INR (n - j) * US.w j n)%R).
 apply Aux.

 (* case [a = t] *)
 rewrite H9.
 rewrite S_INR, Rplus_assoc, (Rplus_comm 1), <-Rplus_assoc. 
 set (X:=(INR (Gr.degree (m1 G) t_) + US.w j n)%R).
 rewrite plus_INR, Rplus_assoc, (Rplus_comm 2), <-Rplus_assoc.
 set (Y:=(INR (Gr.weight (m1 G)) + INR (n - j) * US.w j n)%R).
 apply Aux.

 omega.
 rewrite <-H3; trivial.
 rewrite <-H1, <-(Gr.size_eq H3); apply nat_eqb_true; trivial.
 omega.
 trivial.
 rewrite <-H1; apply nat_eqb_true; trivial.

 (* case [a \notin G1] *)
 fold (US.carV a).
 rewrite US.weighted_choice_spec_notin.
 auto.
 rewrite <-H2; [ | trivial].
 apply leb_complete; change (S (m1 i)) with (1 + m1 i)%nat; 
  rewrite plus_comm; trivial.
 rewrite <-(H2 _ i); [ | trivial]; apply nat_eqb_true; trivial.
 trivialb.
 
 rewrite (@mu_zero Gr.vertex); trivial.

 unfold I, req_mem_rel, andR; intros; expr_simpl; intuition.
 rewrite (H _ L); trivial.

 (* Continuing... *)
 
 Opaque Vset.add.

 apply equiv_eequiva.
 eqobsrel_tail; unfold implMR, I, req_mem_rel, andR;
  simpl; unfold O.eval_op; simpl; repeat split; intuition; mem_upd_simpl.

 rewrite (H0 _ v), (H2 _ L), (H2 _ i); trivial.
 intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl. 
   rewrite (H0 _ v); trivial.
   unfold EP1, P' in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
   apply Gr.in_graph_remove_vertex; auto.
   generalize H6; mem_upd_simpl; clear H6; intro.
   rewrite <-(H0 _ v); [ | trivial].
   generalize (Gr.v_eqb_spec (m1 v) x); destruct (Gr.v_eqb (m1 v) x); intro.
   subst.
   apply Gr.edge_vertex in H6; destruct H6.
   contradict H6; apply Gr.remove_vertex_eq.
   generalize (Gr.v_eqb_spec (m1 v) y); destruct (Gr.v_eqb (m1 v) y); intro. 
   subst.
   apply Gr.edge_vertex in H6; destruct H6.
   contradict H11; apply Gr.remove_vertex_eq.
   apply Gr.in_graph_remove_edge_neq; trivial.
   apply H8.
   apply Gr.in_graph_remove_edge_conv in H6; trivial.
   unfold EP, P1; expr_simpl; mem_upd_simpl.
   unfold EP1, P' in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
   simpl; rewrite H7.
   apply orb_prop in H7.
   rewrite <-(H0 _ v); [ | trivial].
   unfold EP, P1 in H3.
   simpl in H3; unfold O.eval_op in H3; simpl in H3.
   destruct H7; apply orb_prop in H6; destruct H6.
     generalize H3; clear H3.
     case (existsb (Gr.v_eqb u_) (m1 L) || existsb (Gr.v_eqb t_) (m1 L)); intro.
     rewrite H3; trivial.
     apply Gr_v_eqb_true in H6; rewrite <-H6.
     apply Gr.remove_vertex_diff_1 with t_; trivial.
     destruct H3; split.
     rewrite Gr.in_graph_edge_sym; trivial.
     intros x y Hin; decompose [and or] (H7 x y Hin); clear H7; subst; intuition.
     rewrite H6 in H3; simpl in H3; rewrite H3; trivial.
     generalize H3; clear H3.
     case (existsb (Gr.v_eqb u_) (m1 L) || existsb (Gr.v_eqb t_) (m1 L)); intro.
     rewrite H3; trivial.
     apply Gr_v_eqb_true in H6; rewrite <-H6.
     apply Gr.remove_vertex_diff_1 with u_; trivial.
     rewrite H6 in H3; rewrite orb_true_r in H3; rewrite H3; trivial.
   generalize H9; unfold EP1; expr_simpl; mem_upd_simpl.
   intro Heq; apply nat_eqb_true in Heq.
   rewrite Gr.remove_vertex_size; [ | trivial].
   rewrite Heq.
   replace (pred (n - m1 i))%nat with (n - (m1 i + 1))%nat by omega.
   apply nat_eqb_refl.
   generalize H4; clear H4; expr_simpl; intro Heq.
   apply nat_eqb_true in Heq; rewrite Heq, plus_comm; apply nat_eqb_refl.

 Close Scope bool_scope.

 (* 3rd proof obligation of while rule *)
 intro j.
 apply equiv_cons with (Q:=req_mem_rel (Vset.singleton v)
   ((I /-\ EP1 (i <! n) /-\ EP1 (i =?= j)) /-\ EP1 P1) /-\ EP1 (v \in G)).

 apply equiv_strengthen_range.
   apply decMR_req_mem_rel; refine (decMR_and 
     (decMR_and I_dec (decMR_and _ _)) _); auto.

 intros k m1 m2 [ [ [_ [_ [_ ?] ] ] [? ?] ] ?] f Hf.
 rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
 simpl DE.eval_support.
 
 apply US.weighted_choice_in_graph.
 apply leb_complete; change (S (m1 i)) with (1 + m1 i)%nat; rewrite plus_comm;
  trivial.
 apply nat_eqb_true; trivial.
 intros; rewrite deno_nil_elim.
 apply Hf; expr_simpl.
 
 eapply equiv_sub; 
  [ | | apply equiv_random with 
   (Q:=req_mem_rel (Vset.singleton v)
    ((I /-\ EP1 (i <! n) /-\ EP1 (i =?= j)) /-\ EP1 P1))].
 unfold eq_support, andR, I, req_mem_rel, kreq_mem, andR, EP, EP1.
 intros.
 decompose [and] H; clear H.
 split.
 rewrite H1 in H2.
 simpl; rewrite H2, H0; trivial.

 unfold forall_random; intros; expr_simpl; mem_upd_simpl.
 repeat split; trivial.
 intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl.
 intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl.
 apply H0; trivial.
 apply H0; trivial.

 unfold req_mem_rel, req_mem, andR; intuition.

 apply equiv_sub with 
 (P:= req_mem_rel (Vset.singleton v) 
  ((I /-\ EP1 (v \in G) /-\ EP1 (i <! n) /-\ EP1 (i =?= j)) /-\ EP1 P1)) 
 (Q:= req_mem_rel {{ i, G, L, v}}  ((I /-\ EP1 (i =?= S j)) /-\ EP1 P1)).
 unfold I, req_mem_rel, andR; intros; decompose [and] H;  repeat split; intuition.
 unfold I, req_mem_rel, kreq_mem, andR; intuition.
 eqobsrel_tail; unfold implMR, I, req_mem_rel, andR;
   simpl; unfold O.eval_op; simpl; repeat split; intuition; mem_upd_simpl.
 unfold EP1, EP in *; rewrite H2 in H3.
 assert  (kreq_mem {{ i, G, L, v}} m1 m2).
 intros ? ? Hin; Vset_mem_inversion Hin; subst; auto.
 apply req_mem_weaken with (2:=H6); vm_compute; trivial.
 intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl; auto.
 rewrite (H _ i); trivial.
 rewrite (H _ L), (H0 _ v); trivial.

 unfold EP1, EP in *; rewrite H2 in H3; rewrite H3, H0.
 apply Gr.in_graph_remove_vertex; auto.
 
 trivial.

 generalize H6; mem_upd_simpl; clear H6; intro.
 rewrite <-(H0 _ v); [ | trivial].
 generalize (Gr.v_eqb_spec (m1 v) x); destruct (Gr.v_eqb (m1 v) x); intro.
 subst.
 apply Gr.edge_vertex in H6; destruct H6.
 contradict H6; apply Gr.remove_vertex_eq.
 
 generalize (Gr.v_eqb_spec (m1 v) y); destruct (Gr.v_eqb (m1 v) y); intro. 
 subst.
 apply Gr.edge_vertex in H6; destruct H6.
 contradict H11; apply Gr.remove_vertex_eq.

 apply Gr.in_graph_remove_edge_neq; trivial.
 apply H8.
 apply Gr.in_graph_remove_edge_conv in H6; trivial.

 unfold EP, P1; expr_simpl; mem_upd_simpl.
 unfold EP1 in H2; unfold EP in H3; rewrite H2 in H3.
 rewrite H3, H0; trivial.
 simpl in H2; unfold O.eval_op in H2; simpl in H2.
 apply orb_prop in H2; destruct H2; simpl; rewrite H2.
 rewrite orb_true_r; simpl; trivial.
 rewrite orb_true_r, orb_true_r; simpl; trivial.

 generalize H9; clear H9; unfold EP1; expr_simpl; mem_upd_simpl; intro Heq.
 rewrite Gr.remove_vertex_size; [ | trivial].
 apply nat_eqb_true in Heq.
 rewrite Heq.
 replace (pred (n - m1 i))%nat with (n - (m1 i + 1))%nat by omega.
 apply nat_eqb_refl.

 unfold EP1 in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
 apply nat_eqb_true in H7; rewrite H7; rewrite plus_comm; apply nat_eqb_refl.
 
 unfold EP1, P1 in H2; simpl in H2; unfold O.eval_op in H2; simpl in H2.
 apply orb_prop in H2; destruct H2; rewrite H2.
 rewrite orb_true_r; simpl; trivial.
 rewrite orb_true_r, orb_true_r; simpl; trivial.

 (* 4th proof obligation of while rule: Property Stability *)
 apply stability. 
 apply stability.

 (* 5th proof obligation of while rule: Termination *)
 intros k m1 m2 _; split; refine (ford_eq_intro _); apply loop_sem.
Qed.




(*  We bound [ Pr [c(G1)=L] / Pr [c(G2)=L] ] when G1 = G2 + {(t,u)}  *)

Definition Pre2 k (m1 m2:Mem.t k) :=
 (Gr.size (m1 G) = Gr.size (m2 G)) /\
 (forall x, Gr.in_graph (m1 G) x = Gr.in_graph (m2 G) x) /\
 (forall x y, Gr.in_graph_edge (m2 G) x y -> Gr.in_graph_edge (m1 G) x y) /\
 Gr.size (m1 G) = n /\ 
 Gr.in_graph_edge (m1 G) t_ u_ /\
 (forall x y, Gr.in_graph_edge (m1 G) x y -> 
   Gr.in_graph_edge (m2 G) x y \/ (x = t_ /\ y = u_) \/ (x = u_ /\ y = t_)).

Definition I' : mem_rel :=
 req_mem_rel {{i, L}}
 ((fun k m1 m2 => 
   (forall x, Gr.in_graph (m1 G) x = Gr.in_graph (m2 G) x) /\
   forall x y, Gr.in_graph_edge (m2 G) x y -> Gr.in_graph_edge (m1 G) x y) /-\
  (fun k m1 m2 => 
   if EP k P1 m1 then m1 G = m2 G 
   else 
    Gr.in_graph_edge (m1 G) t_ u_ /\
    forall x y, Gr.in_graph_edge (m1 G) x y ->
     Gr.in_graph_edge (m2 G) x y \/ (x = t_ /\ y = u_) \/ (x = u_ /\ y = t_)) /-\
  EP1 (|G| =?= n -! i)).  

Hypothesis I'_dec : decMR I'.

Definition lam1' (j:nat) := 1%R.
Definition lam2' := exp (eps / 4).
Definition lam' (k:nat) := (ProdRR lam1' 0 n * lam2')%R.

Lemma lam2'_ge_1 : (1 <= lam2')%R.
Proof.
 rewrite <-exp_0.
 apply exp_monotonic.
 apply Rdiv_pos.
 apply Rlt_le; apply eps_pos.
 fourier.
Qed.

Lemma lam'_ge_1 : forall k, (k < n)%nat -> (1 <= lam' k)%R.
Proof.
 intros; unfold lam'.
 rewrite <-Rmult_1_l at 1; apply Rmult_le_compat;
  [fourier | fourier | | ]. 
   apply ProdRR_ge_1; intros; apply Rle_refl. 
   apply lam2'_ge_1.
Qed.

Hint Resolve lam2'_ge_1 lam'_ge_1 I'_dec.


Lemma diff_private' :
 eequiva Pre2 E c E c Post (fun _ => lam' 0) (fun _ => 0).
Proof.
 intros; unfold c.
 set (P:=Pre2 /-\ EP1 (n =?= |G|) /-\ EP1 (i =?= O) /-\ EP1 (L =?= Nil _)).
 eapply eequiva_weaken; [ | | | | eapply eequiva_seq with 
   (lam :=fun _ => 1%R) (lam':=fun _ => lam' O) 
   (ep  :=fun _ => 0) (ep' :=fun _ => 0)
   (P:=req_mem_rel Vset.empty Pre2) (Q:=Post) 
   (Q':=req_mem_rel {{i,L}} P)]; trivial.
   unfold req_mem_rel, andR; split; [apply req_mem_empty | trivial].
   intros; simpl; rewrite Rmult_1_l; trivial. 
   intros k; rewrite multRU_0_r, Uplus_zero_left; trivial.
   auto.
 (* Initialization *)
 apply equiv_eequiva.
 eqobsrel_tail; unfold implMR, req_mem_rel, P, Pre2, EP1, andR; simpl;
   intros; decompose [and] H; clear H; repeat split; expr_simpl. 
 rewrite H4; apply nat_eqb_refl.

 (* While loop *)
 assert (HI1:implMR I' (EP_eq_expr (i <! n) (i <! n))).
   unfold implMR, I', req_mem_rel, andR; intuition.
   unfold EP_eq_expr; simpl; unfold O.eval_op; simpl; rewrite H0; trivial.
 assert (HI2:implMR I' (EP_eq_expr P1 P2)).
   unfold implMR, I', req_mem_rel, andR; intros; intuition.
   unfold EP_eq_expr; simpl; unfold O.eval_op; simpl; rewrite H0; trivial.

 eapply eequiva_weaken with (lam':=fun _ => lam' 0) (ep' :=fun _ => 0)
  (P':=I' /-\ EP1 (i =?= O) /-\ EP1 (!P1)) (Q':=I' /-\ EP1 (!i <! n));
  [ | | | | apply eequiva_while_split with (P2:=P2)
    (lam1:=lam1') (lam2:=lam2') (n:=n)]; trivial.

 unfold implMR, I', P, Pre2, req_mem_rel, andR, P1.
 intros k m1 m2 H; decompose [and] H; clear H.
 generalize H3, H7, H10; clear H3 H7 H10; expr_simpl; intros.
 apply nat_eqb_true in H3; apply nat_eqb_true in H7.
 generalize (eqb_list_spec Gr.v_eqb Gr.v_eqb_spec (m1 L) (@nil Gr.vertex)).
 rewrite H10; clear H10; intro.
 repeat split; trivial.
 unfold EP; expr_simpl.
 rewrite H; simpl; split; trivial.
 rewrite H7, H3, <-minus_n_O; apply nat_eqb_refl.
 rewrite H3; apply nat_eqb_refl.
 rewrite H; trivial.
 unfold implMR, I', Post, req_mem_rel, andR, P1; intuition.
 apply req_mem_weaken with (2:=H); vm_compute; trivial.
 6:intros; auto.
 Focus 6.
 intros; unfold lam; apply Rmult_le_compat; [ | | | trivial].
 rewrite <-ProdRR_ge_1; [fourier | trivial].
 rewrite <-lam2'_ge_1; fourier.
 apply ProdRR_ge_1_monotonic; trivial.

 (* 1st proof obligation of while rule *)
 intro j.
 set (P':=(t is_in (v |::| L)) || (u is_in (v |::| L))).
 apply eequiva_eq_compat_l with 
  ([ v <$- choose G i n; Assert !P' ] ++
   [ L <- v |::| L; G <- G \ v; i <- i +! 1%nat]).
   intros; simpl app. 
   repeat elim_random.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m''.
   repeat (elim_assign || elim_assert).
   match goal with 
    |- (match ?C1' with |true => _ |false => _ end) == 
       (match ?C2' with |true => _ |false => _ end) => 
       assert (C1' = C2') by (expr_simpl; apply f_equal;
         rewrite <- H0; simpl; mem_upd_simpl)
   end.
   rewrite <- H0.
   case_eq (E.eval_expr (!P') (m1{!v <-- m''!})); intro HP; simpl O.tres in HP;
    rewrite HP; trivial.
   repeat elim_assign; rewrite deno_nil_elim.
   mem_upd_simpl; trivial.

 apply eequiva_eq_compat_r with 
  ([ v <$- choose G i n; Assert !P' ] ++
   [ L <- v |::| L; G <- G \ v; i <- i +! 1%nat]).
   intros; simpl app. 
   repeat elim_random.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m''.
   repeat (elim_assign || elim_assert).
   match goal with 
    |- (match ?C1' with |true => _ |false => _ end) == 
       (match ?C2' with |true => _ |false => _ end) => 
       assert (C1' = C2') by (expr_simpl; apply f_equal; 
         rewrite <- H0; simpl; mem_upd_simpl)
   end.
   rewrite <- H0.
   case_eq (E.eval_expr (!P') (m2{!v <-- m''!})); intro HP; simpl O.tres in HP; 
    rewrite HP; trivial.
   repeat elim_assign; rewrite deno_nil_elim.
   mem_upd_simpl; trivial.

 eapply eequiva_weaken with (lam':=fun _ => (lam1' j * 1)%R) (ep' :=fun _ => 0 + _ ** 0)
  (Q':=req_mem_rel Vset.empty (I' /-\ EP1 (i =?= S j) /-\ EP1 (!P1)));
  [ | | | | apply eequiva_seq with (Q':=req_mem_rel {{v}} 
     (EP1 (v \in G) /-\ I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (!P'))) ].
   trivial.
   unfold implMR, I', req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H.
   generalize H5, H7, H8; clear H5 H7 H8; expr_simpl; intros.
   apply nat_eqb_true in H5; apply nat_eqb_true in H7.
   rewrite negb_orb in H8; apply andb_prop in H8; destruct H8 as [H9 H10].
   repeat split; trivial.
   rewrite H7; apply nat_eqb_refl.
   rewrite H5; apply nat_eqb_refl.
   rewrite negb_orb, H9, H10; trivial.
   intros; rewrite Rmult_1_r; trivial.
   intros ?; rewrite multRU_0_r, Uplus_zero_left; trivial.
   trivial.

 apply eequiva_weaken with (lam':=fun _ => lam1' j) (ep' := fun _ => 0)
   (P':=(I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (!P1)) /-\ 
       (I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j)))
   (Q':=((req_mem_rel {{v}} (EP1 (!P')) /-\ EP1 (v \in G)) /-\ 
   (I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j)))); trivial.
   unfold implMR, I', req_mem_rel, andR; intuition.
   unfold implMR, req_mem_rel, andR; intuition.
 apply eequiva_inv_Modify with {{i,G,L}} {{i,G,L}} {{v}} {{v}}; trivial.
   unfold depend_only_rel, I', req_mem_rel, andR, EP1; intuition. 
   apply req_mem_trans with m1.
     apply req_mem_sym; apply req_mem_weaken with (2:=H).
     vm_compute; trivial.
     apply req_mem_trans with m2; trivial.
     apply req_mem_weaken with (2:=H0); apply eq_refl.
   rewrite <-(H _ G), <-(H0 _ G); trivial.
   generalize H6; rewrite <-(H _ G), <-(H0 _ G); auto.
   unfold EP, P1; expr_simpl; rewrite <-(H _ G), <-(H0 _ G), <-(H _ L); trivial.
   expr_simpl; rewrite <-(H _ i), <-(H _ G); auto.
   expr_simpl; rewrite <-(H _ i); trivial.
   expr_simpl; rewrite <-(H _ i); trivial.
   apply modify_correct with (refl1_info (empty_info E E)) Vset.empty; apply eq_refl.
   apply modify_correct with (refl1_info (empty_info E E)) Vset.empty; apply eq_refl.
 
 apply eequiva_range_l.
   intros k m1 m2 [ [H' [_ [_ ?] ] ] [? _] ] f Hf.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   simpl DE.eval_support.
   apply US.weighted_choice_in_graph.
     unfold EP1 in H0; simpl in H0; unfold O.eval_op in H0; simpl in H0.
     rewrite plus_comm in H0; apply leb_complete; trivial.
     apply nat_eqb_true; trivial.
     intros; rewrite deno_assert_elim.
     case (@E.eval_expr _ T.Bool (!P') (m1{!v <-- x!}));
       [ apply Hf; expr_simpl | trivial ].

 (* Random sampling *)
 apply eequiva_weaken with (lam':=fun _ => lam1' j) (ep' :=fun _ => 0)
  (P':=I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (!P1))
  (Q':=EP_eq_expr v v /-\ EP1 (!P') /-\ EP2 (!P'));
  [ | | | |  apply eequiva_random_assert_strong ]; trivial.
  unfold implMR, req_mem_rel, andR, EP_eq_expr; intuition.
  intros ? ? Hin; Vset_mem_inversion Hin; subst; trivial.
  
 unfold I', req_mem_rel, andR; intros; decompose [and] H; clear H.
 unfold EP1 in H8; unfold EP in H0; rewrite eval_negb in H8;
   apply is_true_negb in H8; apply not_is_true_false in H8. 
 rewrite H8 in H0; destruct H0.
 unfold P1 in H8; simpl in H8; unfold O.eval_op in H8; simpl in H8;
   apply orb_false_elim in H8; destruct H8.
 match goal with |- le_dist_asym ?D1' ?D2' _ _ => 
   assert (HdL: is_Discrete D1'); [ | assert (HdR: is_Discrete D2') ] 
 end.
   apply (is_Discrete_Mlet _ (DE.discrete_support _ _)).
   intros a; case (@E.eval_expr _ T.Bool (!P') (m1 {!v <-- a!}));
    [ apply is_Discrete_Munit | apply 
      (is_Discrete_distr0  (T.default k (T.User Vertex))) ].
   apply (is_Discrete_Mlet _ (DE.discrete_support _ _)).
   intros a; case (@E.eval_expr _ T.Bool (!P') (m2 {!v <-- a!}));
    [ apply is_Discrete_Munit | apply 
      (is_Discrete_distr0  (T.default k (T.User Vertex))) ].
 eapply le_dist_asym_weaken_ep; [ |
  eapply le_dist_asym_discr_pointwise_ub with (F:=fun _ => 0) ].
   rewrite serie_zero; auto.
   apply carT_cover.
   apply Rle_refl.
   apply (disc_eqpoint_r HdR HdL).
   apply (disc_eqpoint_l HdR HdL).
  
 intro; simpl; expr_simpl.
 rewrite (H2 _ i); [ | trivial].

 Open Scope bool_scope.

 unfold lam1'; rewrite multRU_1_l.
 transitivity 
  (mu (US.weighted_choice (m1 G) (m2 i) n)
    (fun x => 
     if (negb (Gr.v_eqb u_ a || Gr.v_eqb t_ a) && Gr.v_eqb a x) then 1 else 0) -
   (mu (US.weighted_choice (m2 G) (m2 i) n)
     (fun x =>
      if (negb (Gr.v_eqb u_ a || Gr.v_eqb t_ a) && Gr.v_eqb a x) then 1 else 0))).
   apply Uminus_le_compat.
     refine (mu_monotonic _ _ _ _); intro; mem_upd_simpl.
     rewrite H7, H8, orb_false_r, orb_false_r; trivial.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     rewrite andb_true_r; unfold carT; simpl.
     case (negb (Gr.v_eqb u_ x || Gr.v_eqb t_ x)); trivial.
     rewrite andb_false_r; unfold carT; simpl.
     case (negb (Gr.v_eqb u_ x || Gr.v_eqb t_ x)); trivial.
     simpl.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro.
      tauto.
      trivial.
     refine (mu_monotonic _ _ _ _); intro; mem_upd_simpl.
     rewrite <-(H2 _ L), H7, H8, orb_false_r, orb_false_r; trivial.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     rewrite andb_true_r; unfold carT; simpl.
     case (negb (Gr.v_eqb u_ x || Gr.v_eqb t_ x)); trivial.
     simpl; rewrite Gr_v_eqb_refl; trivial.
     rewrite andb_false_r; unfold carT; simpl.
     trivial.
 
 apply Uminus_le_zero.
 case_eq (negb (Gr.v_eqb u_ a || Gr.v_eqb t_ a)); intro Heq; simpl.
 case_eq (Gr.in_graph (m2 G) a); intro Ha.

 (* case [a in (m2 G) ] *)
 rewrite negb_orb in Heq; apply andb_prop in Heq.
 generalize H1, H4; clear H1 H4; unfold EP1; expr_simpl; intros.
 apply leb_complete in H4; apply nat_eqb_true in H1.
 rewrite <-H2; trivial; rewrite H1 in *; fold (US.carV a).
 rewrite <-retract_U, US.weighted_choice_spec_in.
 rewrite <-(retract_U (mu (US.weighted_choice (m2 G) j n) (US.carV a))),
   US.weighted_choice_spec_in.
 apply iU_le_morphism.
 generalize (Gr.eqb_spec (m1 G) (m2 G)); case (Gr.eqb (m1 G) (m2 G)); intro HG.

 rewrite HG; trivial.

 rewrite <-Gr.weight_diff with (G1:=m2 G) (G2:=m1 G) (t_:=t_) (u_:=u_); trivial.
 assert (Gr.degree (m1 G) a = Gr.degree (m2 G) a).
   destruct Heq as [X1 X2]; apply negb_true_iff in X1; apply negb_true_iff in X2.
   symmetry; apply Gr.degree_diff_neq with t_ u_; auto.
   generalize (Gr.v_eqb_spec t_ a); destruct (Gr.v_eqb t_ a);
     [discriminate | apply not_eq_sym; trivial].
   generalize (Gr.v_eqb_spec u_ a); destruct (Gr.v_eqb u_ a);
     [discriminate | apply not_eq_sym; trivial].
 rewrite H9.
 apply Rdiv_le.
   rewrite <-Rplus_0_l at 1; apply Rplus_le_lt_compat; [ auto |
     apply Rmult_lt_0_compat; [ apply lt_0_INR | apply US.w_pos]; omega ].
   rewrite <-Rplus_0_l at 1; apply Rplus_le_lt_compat; [ auto |
     apply Rmult_lt_0_compat; [ apply lt_0_INR | apply US.w_pos]; omega ].
 apply Rfourier_le.
   rewrite plus_INR, Rplus_assoc, (Rplus_comm (INR 2%nat)).
   apply Rplus_le_compat_l, Rle_plus_l; auto.
   rewrite <-Rplus_0_l at 1; apply Rplus_le_lt_compat; [ auto | apply US.w_pos ].
 
 omega.
 apply not_eq_sym; trivial.
 auto.
 omega.
 auto.
 apply nat_eqb_true; rewrite <-H1.
 rewrite <-(Gr.size_eq H3); trivial.
 omega.
 rewrite H3; trivial.
 apply nat_eqb_true; rewrite <-H1; trivial.

 (* a \notin G1 *)
 fold (US.carV a).
 rewrite US.weighted_choice_spec_notin.
 auto.
 rewrite <-H2; [ | trivial].
 apply leb_complete; change (S (m1 i)) with (1 + m1 i)%nat; 
  rewrite plus_comm; trivial.
 rewrite <-H2; [ | trivial]; apply nat_eqb_true; trivial.
 rewrite H3; trivialb.

 rewrite (@mu_zero Gr.vertex); trivial.

 unfold I', req_mem_rel, kreq_mem, andR; intros; decompose [and] H.
 unfold P'; expr_simpl.
 rewrite (H2 _ L).
 trivial.
 vm_compute; trivial.

 (* Continuing... *)
 
 Opaque Vset.add.

 apply equiv_eequiva.
 eqobsrel_tail; unfold implMR, I', req_mem_rel, andR;
  simpl; unfold O.eval_op; simpl; repeat split; intuition; mem_upd_simpl.
   rewrite (H0 _ v), (H2 _ L), (H2 _ i); trivial.
   intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl. 
   rewrite (H0 _ v); trivial.
   unfold EP1, P' in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
   apply Gr.in_graph_remove_vertex; auto.
   generalize H6; mem_upd_simpl; clear H6; intro.
   generalize (Gr.v_eqb_spec (m1 v) x); destruct (Gr.v_eqb (m1 v) x); intro.
   subst.
   apply Gr.edge_vertex in H6; destruct H6.
   contradict H6; rewrite (H0 _ v); trivial; apply Gr.remove_vertex_eq.
   generalize (Gr.v_eqb_spec (m1 v) y); destruct (Gr.v_eqb (m1 v) y); intro. 
   subst.
   apply Gr.edge_vertex in H6; destruct H6.
   contradict H11; rewrite (H0 _ v); trivial; apply Gr.remove_vertex_eq.
   apply Gr.in_graph_remove_edge_neq; trivial.
   apply H8.
   apply Gr.in_graph_remove_edge_conv in H6; trivial.

   unfold EP, P1; expr_simpl; mem_upd_simpl.
   unfold EP1, P' in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
   rewrite negb_orb in H7; apply andb_prop in H7; destruct H7.
   rewrite negb_orb in H6, H7; apply andb_prop in H6; apply andb_prop in H7.
   destruct H6; destruct H7.
   simpl; rewrite negb_true_iff in H6, H7, H10, H11; rewrite H6, H7, H10, H11; simpl.
   assert (W:EP k P1 m1 = false) by 
    (unfold EP, P1; expr_simpl; rewrite H10, H11; trivial).
   rewrite W in H3; clear W; destruct H3.
   split.
     apply Gr.in_graph_remove_edge_neq; trivial.
     intro Heq; rewrite Heq in H7.
     rewrite Gr_v_eqb_refl in H7; discriminate H7.
     intro Heq; rewrite Heq in H6.
     rewrite Gr_v_eqb_refl in H6; discriminate H6.
     intros.
     generalize (Gr.v_eqb_spec (m2 v) x); destruct (Gr.v_eqb (m2 v) x); intro Hx. 
     subst.
     apply Gr.edge_vertex in H13; destruct H13.
     contradict H13; rewrite <-(H0 _ v); trivial; apply Gr.remove_vertex_eq.
     generalize (Gr.v_eqb_spec (m2 v) y); destruct (Gr.v_eqb (m2 v) y); intro Hy. 
     subst.
     apply Gr.edge_vertex in H13; destruct H13.
     contradict H14; rewrite <-(H0 _ v); trivial; apply Gr.remove_vertex_eq.
     apply Gr.in_graph_remove_edge_conv in H13. 
     decompose [and or] (H12 _ _ H13); clear H12 H13; trivial; subst.     
       left; apply Gr.in_graph_remove_edge_neq; trivial.
       right; auto.
       right; auto.
   generalize H9; unfold EP1; expr_simpl; mem_upd_simpl.
   intro Heq; apply nat_eqb_true in Heq.
   rewrite Gr.remove_vertex_size; [ | trivial].
   rewrite Heq.
   replace (pred (n - m1 i))%nat with (n - (m1 i + 1))%nat by omega.
   apply nat_eqb_refl.
   generalize H4; clear H4; expr_simpl; intro Heq.
   apply nat_eqb_true in Heq; rewrite Heq, plus_comm; apply nat_eqb_refl.

 (* 2nd proof obligation of while rule *)
 Close Scope bool_scope.
 intro j.
 set (P':=(t is_in (v |::| L)) || (u is_in (v |::| L))).
 apply eequiva_eq_compat_l with 
  ([ v <$- choose G i n; Assert P' ] ++
   [ L <- v |::| L; G <- G \ v; i <- i +! 1%nat]).
   intros; simpl app. 
   repeat elim_random.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m''.
   repeat (elim_assign || elim_assert).
   match goal with 
    |- (match ?C1' with |true => _ |false => _ end) == 
       (match ?C2' with |true => _ |false => _ end) => 
       assert (C1' = C2') by (expr_simpl; apply f_equal;
         rewrite <- H0; simpl; mem_upd_simpl)
   end.
   rewrite <- H0.
   case_eq (E.eval_expr (P') (m1{!v <-- m''!})); intro HP; simpl O.tres in HP;
    rewrite HP; trivial.
   repeat elim_assign; rewrite deno_nil_elim.
   mem_upd_simpl; trivial.

 apply eequiva_eq_compat_r with 
  ([ v <$- choose G i n; Assert P' ] ++
   [ L <- v |::| L; G <- G \ v; i <- i +! 1%nat]).
   intros; simpl app. 
   repeat elim_random.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m''.
   repeat (elim_assign || elim_assert).
   match goal with 
    |- (match ?C1' with |true => _ |false => _ end) == 
       (match ?C2' with |true => _ |false => _ end) => 
       assert (C1' = C2') by (expr_simpl; apply f_equal; 
         rewrite <- H0; simpl; mem_upd_simpl)
   end.
   rewrite <- H0.
   case_eq (E.eval_expr (P') (m2{!v <-- m''!})); intro HP; simpl O.tres in HP; 
    rewrite HP; trivial.
   repeat elim_assign; rewrite deno_nil_elim.
   mem_upd_simpl; trivial.

 eapply eequiva_weaken with (lam':=fun _ => (lam2' * 1)%R) (ep' :=fun _ => 0 + _ ** 0)
  (Q':=req_mem_rel Vset.empty (I' /-\ EP1 (i =?= S j) /-\ EP1 (P1)));
  [ | | | | apply eequiva_seq with (Q':=req_mem_rel {{v}} 
     (EP1 (v \in G) /-\ I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (P'))) ].
   trivial.
   unfold implMR, req_mem_rel, andR; intuition.
   intros; rewrite Rmult_1_r; trivial.
   intros ?; rewrite multRU_0_r, Uplus_zero_left; trivial.
   trivial.

 apply eequiva_weaken with (lam':=fun _ => lam2') (ep' := fun _ => 0)
   (P':=(I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (!P1)) /-\ 
       (I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j)))
   (Q':=((req_mem_rel {{v}} (EP1 P') /-\ EP1 (v \in G)) /-\ 
   (I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j)))); trivial.
   unfold implMR, I', req_mem_rel, andR; intuition.
   unfold implMR, req_mem_rel, andR; intuition.
 apply eequiva_inv_Modify with {{i,G,L}} {{i,G,L}} {{v}} {{v}}; trivial.
   unfold depend_only_rel, I', req_mem_rel, andR, EP1; intuition. 
   apply req_mem_trans with m1.
     apply req_mem_sym; apply req_mem_weaken with (2:=H).
     vm_compute; trivial.
     apply req_mem_trans with m2; trivial.
     apply req_mem_weaken with (2:=H0); apply eq_refl.
   rewrite <-(H _ G), <-(H0 _ G); trivial.
   generalize H6; rewrite <-(H _ G), <-(H0 _ G); auto.
   unfold EP, P1; expr_simpl; rewrite <-(H _ G), <-(H0 _ G), <-(H _ L); trivial.
   expr_simpl; rewrite <-(H _ i); trivial.
   generalize H8; expr_simpl; rewrite <-(H _ G); trivial.
   expr_simpl; rewrite <-(H _ i); trivial.
   expr_simpl; rewrite <-(H _ i); trivial.
   apply modify_correct with (refl1_info (empty_info E E)) Vset.empty; apply eq_refl.
   apply modify_correct with (refl1_info (empty_info E E)) Vset.empty; apply eq_refl.
 
 apply eequiva_range_l.
   intros k m1 m2 [ [_ [_ [_ ?] ] ] [? _] ] f Hf.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   simpl DE.eval_support.
   apply US.weighted_choice_in_graph.
     apply leb_complete; change (S (m1 i)) with (1 + m1 i)%nat; rewrite plus_comm; 
       trivial.
     apply nat_eqb_true; trivial.
     intros; rewrite deno_assert_elim.
     case (@E.eval_expr _ T.Bool P' (m1{!v <-- x!}));
       [ apply Hf; expr_simpl | trivial ].

 (* Random sampling *)
 apply eequiva_weaken with (lam':=fun _ => lam2') (ep' :=fun _ => 0)
  (P':=I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j) /-\ EP1 (!P1))
  (Q':=EP_eq_expr v v /-\ EP1 P' /-\ EP2 P');
  [ | | | |  apply eequiva_random_assert_strong ]; trivial.
  unfold implMR, req_mem_rel, andR, EP_eq_expr; intuition.
  intros ? ? Hin; Vset_mem_inversion Hin; subst; trivial.
  
 unfold I', req_mem_rel, andR; intros; decompose [and] H;
   clear H; simpl; expr_simpl.
 unfold EP1 in H8; unfold EP in H0; rewrite eval_negb in H8.
 apply is_true_negb in H8; apply not_is_true_false in H8;
   rewrite H8 in H0; destruct H0.
 unfold P1 in H8; simpl in H8; unfold O.eval_op in H8; simpl in H8.
 apply orb_false_elim in H8; destruct H8.
 match goal with |- le_dist_asym ?D1' ?D2' _ _ => 
   assert (HdL: is_Discrete D1'); [ | assert (HdR: is_Discrete D2') ] 
 end.
   apply is_Discrete_Mlet.
   unfold US.weighted_choice.
   destruct (le_lt_dec n (m1 i)); [ apply is_Discrete_Munit | ].
   destruct (Gr_is_empty_dec (m1 G)); [ apply is_Discrete_Munit | ].
   destruct (Gr.not_is_empty (g:=m1 G) n0); apply finite_distr_discrete.
   intro a.
    match goal with |- context [is_Discrete (if ?CC then _ else _)] => 
      destruct CC end.
   apply is_Discrete_Munit.
   apply (is_Discrete_distr0 (T.default k (T.User Vertex))).
   apply is_Discrete_Mlet.
   unfold US.weighted_choice.
   destruct (le_lt_dec n (m2 i)); [ apply is_Discrete_Munit | ].
   destruct (Gr_is_empty_dec (m2 G)); [ apply is_Discrete_Munit | ].
   destruct (Gr.not_is_empty (g:=m2 G) n0); apply finite_distr_discrete.
   intro a.
    match goal with |- context [is_Discrete (if ?CC then _ else _)] => 
      destruct CC end.
   apply is_Discrete_Munit.
   apply (is_Discrete_distr0 (T.default k (T.User Vertex))).
 eapply le_dist_asym_weaken_ep; [ |
  eapply le_dist_asym_discr_pointwise_ub with (F:=fun _ => 0) ].
   rewrite serie_zero; auto.
   apply US.carV_prop.
   trivial.
   apply (disc_eqpoint_r HdR HdL).
   apply (disc_eqpoint_l HdR HdL).
  
 Open Scope bool_scope.
 intro; simpl; expr_simpl.
 rewrite (H2 _ i); [ | trivial].

 transitivity 
  (mu (US.weighted_choice (m1 G) (m2 i) n)
    (fun x => 
     if ((Gr.v_eqb u_ a || Gr.v_eqb t_ a) && Gr.v_eqb a x) then 1 else 0) -
   lam2' **
   (mu (US.weighted_choice (m2 G) (m2 i) n)
     (fun x =>
      if ((Gr.v_eqb u_ a || Gr.v_eqb t_ a) && Gr.v_eqb a x) then 1 else 0))).
   apply Uminus_le_compat.
     refine (mu_monotonic _ _ _ _); intro; mem_upd_simpl.
     rewrite H7, H8, orb_false_r, orb_false_r; trivial.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     rewrite andb_true_r; unfold carT; simpl.
     case (Gr.v_eqb u_ x || Gr.v_eqb t_ x); trivial.
     rewrite andb_false_r; unfold carT; simpl.
     case (Gr.v_eqb u_ x || Gr.v_eqb t_ x); trivial.
     unfold US.carV; simpl.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     tauto.
     trivial.
     apply multRU_le_compat.
     rewrite <-lam2'_ge_1; fourier.
     trivial.
     refine (mu_monotonic _ _ _ _); intro; mem_upd_simpl.
     rewrite <-(H2 _ L), H7, H8, orb_false_r, orb_false_r; trivial.
     generalize (Gr.v_eqb_spec a x); destruct (Gr.v_eqb a x); intro; subst.
     rewrite andb_true_r; unfold  US.carV, carT; simpl.
     case (Gr.v_eqb u_ x || Gr.v_eqb t_ x); trivial.
     simpl; rewrite Gr_v_eqb_refl; trivial.
     rewrite andb_false_r; unfold carT; simpl.
     trivial.
 
 apply Uminus_le_zero.
 case_eq (Gr.v_eqb u_ a || Gr.v_eqb t_ a); intro Heq; simpl.
 case_eq (Gr.in_graph (m1 G) a); intro Ha.

 (* case [a in G1] *)
 apply orb_prop in Heq.
 generalize H4, H1; clear H4 H1; unfold EP1; expr_simpl; intros.
 apply leb_complete in H4; apply nat_eqb_true in H1.
 rewrite <-H2; trivial; rewrite H1 in *.

 fold (US.carV a).
 rewrite <-retract_U, US.weighted_choice_spec_in.
 rewrite <-(retract_U (mu (US.weighted_choice _ _ _) _)),
   US.weighted_choice_spec_in.
 rewrite <-(retract_U (lam2' ** _)); apply iU_le.
 destruct (Rle_dec (lam2' * iR (iU ((INR (Gr.degree (m2 G) a) + US.w j n) /
     (INR (Gr.weight (m2 G)) + INR (n - j) * US.w j n)))) 1%R). 

 (* no overflow *)
 rewrite multRU_Rmult_b, retract_R; trivial.
 generalize (Gr.eqb_spec (m1 G) (m2 G)); case (Gr.eqb (m1 G) (m2 G)); intro HG.
 (* case [m1 G = m2 G] *)
 rewrite HG.
 rewrite <-Rmult_1_l at 1; apply Rmult_le_compat.
 fourier.
 apply Rdiv_pos.
 apply Rplus_le_le_0_compat.
 apply pos_INR.
 apply Rlt_le, US.w_pos; omega.
 apply Rplus_le_lt_0_compat.
 apply pos_INR.
 apply Rmult_lt_0_compat.
 apply lt_0_INR; omega.
 apply US.w_pos; omega.
 apply lam2'_ge_1.
 trivial.
 (* case [m1 G <> m2 G] *)
 rewrite <-Gr.weight_diff with (G1:=m2 G) (G2:=m1 G) (t_:=t_) (u_:=u_); trivial.
 destruct (Gr.degree_diff_eq (G1:=m2 G) (G2:=m1 G) (t_:=t_) (u_:=u_)); trivial.
   apply not_eq_sym; trivial.
   auto.

 assert (Aux: forall G' s, 
   let X := (INR (Gr.degree G' s) + US.w j n)%R in
   let Y := (INR (Gr.weight G') + INR (n - j) * US.w j n)%R in
   ((X + 1) / (Y + 2) <= lam2' * (X / Y))%R).
   intros.
   assert (0 < X)%R by (apply Rplus_le_lt_0_compat; [ auto | apply US.w_pos; omega ]).
   assert (0 < Y)%R by (apply Rplus_le_lt_0_compat; [ auto | 
     apply Rmult_lt_0_compat; [ apply lt_0_INR | apply US.w_pos]; omega ]).

   transitivity (X / Y + 1 / Y)%R.
   unfold Rdiv; rewrite Rmult_plus_distr_r.
   apply Rplus_le_compat.
   apply Rdiv_le.
   fourier.
   fourier.
   apply Rmult_le_compat; try fourier.
   rewrite Rmult_1_l, Rmult_1_l.
   apply Rle_Rinv; fourier.
 
   apply Rmult_le_reg_r with Y; [trivial | ].
   apply Rmult_le_reg_r with (1/X)%R.
   apply Rdiv_lt_0; fourier.
   replace ((X / Y + 1 / Y) * Y * (1 / X))%R with (1 + 1 / X)%R by
     (field; split; apply not_eq_sym, Rlt_not_eq; fourier).
   replace (lam2' * (X / Y) * Y * (1 / X))%R with lam2' by
     (field; split; apply not_eq_sym, Rlt_not_eq; fourier).
   
   unfold lam2'.
   eapply Rle_trans; [apply Rlt_le, exp_ineq1 | ].
   apply Rdiv_lt_0; fourier.
   apply exp_monotonic.
   transitivity (1 / US.w j n)%R.
   apply Rdiv_le; try fourier.
   apply US.w_pos; omega.
   rewrite Rmult_1_l, Rmult_1_l; unfold X.
   rewrite <-Rplus_0_l at 1; apply Rplus_le_compat; trivial.
   
   transitivity (1 / US.w 0 n)%R.
   apply Rdiv_le; try fourier.
   apply US.w_pos; omega.
   apply US.w_pos; omega.
   rewrite Rmult_1_l, Rmult_1_l; unfold US.w.
   apply Rmult_le_compat.
   apply Rdiv_pos.
   fourier.
   trivial.
   apply sqrt_pos.
   trivial.
   apply sqrt_le_1_alt.
   apply Rdiv_le.
   apply lt_0_INR; omega.
   apply lt_0_INR; omega.
   apply Rmult_le_compat.
   auto.
   auto.
   trivial.
   apply le_INR; omega.
   unfold US.w.
   rewrite <-minus_n_O.

   unfold Rdiv at 3; rewrite <-Rinv_r_sym.
   rewrite sqrt_1, Rmult_1_r.
   apply Req_le; field; apply not_eq_sym; apply Rlt_not_eq; trivial.
   apply not_eq_sym; apply Rlt_not_eq; apply lt_0_INR; trivial.

 destruct Heq as [Heq | Heq]; apply Gr_v_eqb_true in Heq; subst a.
 (* case [a = u] *)
 rewrite H10.
 rewrite S_INR, Rplus_assoc, (Rplus_comm 1), <-Rplus_assoc. 
 set (X:=(INR (Gr.degree (m2 G) u_) + US.w j n)%R).
 rewrite plus_INR, Rplus_assoc, (Rplus_comm 2), <-Rplus_assoc.
 set (Y:=(INR (Gr.weight (m2 G)) + INR (n - j) * US.w j n)%R).
 apply Aux.
 (* case [a = t] *)
 rewrite H9.
 rewrite S_INR, Rplus_assoc, (Rplus_comm 1), <-Rplus_assoc. 
 set (X:=(INR (Gr.degree (m2 G) t_) + US.w j n)%R).
 rewrite plus_INR, Rplus_assoc, (Rplus_comm 2), <-Rplus_assoc.
 set (Y:=(INR (Gr.weight (m2 G)) + INR (n - j) * US.w j n)%R).
 apply Aux. 

 apply (not_eq_sym HG).
 auto.
 
 rewrite <-(US.weighted_choice_spec_in).
 apply iR_bound.
 omega.
 rewrite <-H3; trivial.
 rewrite<-H1, <-(Gr.size_eq H3); apply nat_eqb_true; trivial.

 apply Rnot_le_lt in n0.
 unfold multRU.
 match goal with
  |- context [Rle_dec ?x ?y] => destruct (Rle_dec x y)
 end.
 contradict r; apply Rlt_not_le; trivial.
 rewrite iR_1; trivial.
 apply Rdiv_le_1.
 apply Rplus_le_lt_0_compat.
 auto.
 apply Rmult_lt_0_compat.
 apply lt_0_INR; omega.
 apply US.w_pos; omega.
 apply Rplus_le_compat.
 apply le_INR.
 eapply le_trans; [ | apply (Gr.degree_le_weight _ a)]; omega.
 rewrite <-Rmult_1_l at 1.
 apply Rmult_le_compat.
 fourier.
 apply Rlt_le, US.w_pos; omega.
 change 1%R with (INR 1); apply le_INR; omega.
 trivial.

 omega.
 rewrite <-H3; trivial.
 rewrite <-H1, <-(Gr.size_eq H3); apply nat_eqb_true; trivial.
 omega.
 trivial.
 rewrite <-H1; apply nat_eqb_true; trivial.

 (* case [a \notin G1] *)
 fold (US.carV a).
 rewrite US.weighted_choice_spec_notin.
 auto.
 rewrite <-H2; [ | trivial].
 apply leb_complete; change (S (m1 i)) with (1 + m1 i)%nat; 
  rewrite plus_comm; trivial.
 rewrite <-(H2 _ i); [ | trivial]; apply nat_eqb_true; trivial.
 trivialb.
 
 rewrite (@mu_zero Gr.vertex); trivial.

 unfold I', req_mem_rel, andR; intros; expr_simpl; intuition.
 rewrite (H _ L); trivial.


 (* Continuing... *)
 Opaque Vset.add.

 apply equiv_eequiva.
 eqobsrel_tail; unfold implMR, I', req_mem_rel, andR;
  simpl; unfold O.eval_op; simpl; repeat split; intuition; mem_upd_simpl.
   rewrite (H0 _ v), (H2 _ L), (H2 _ i); trivial.
   intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl. 
   rewrite (H0 _ v); trivial.
   unfold EP1, P' in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
   apply Gr.in_graph_remove_vertex; auto.
   generalize H6; mem_upd_simpl; clear H6; intro.
   generalize (Gr.v_eqb_spec (m1 v) x); destruct (Gr.v_eqb (m1 v) x); intro.
   subst.
   apply Gr.edge_vertex in H6; destruct H6.
   contradict H6; rewrite (H0 _ v); trivial; apply Gr.remove_vertex_eq.
   generalize (Gr.v_eqb_spec (m1 v) y); destruct (Gr.v_eqb (m1 v) y); intro. 
   subst.
   apply Gr.edge_vertex in H6; destruct H6.
   contradict H11; rewrite (H0 _ v); trivial; apply Gr.remove_vertex_eq.
   apply Gr.in_graph_remove_edge_neq; trivial.
   apply H8.
   apply Gr.in_graph_remove_edge_conv in H6; trivial.

   unfold EP, P1; expr_simpl; mem_upd_simpl.
   unfold EP1, P' in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
   simpl; rewrite H7.
   apply orb_prop in H7.
   rewrite <-(H0 _ v); [ | trivial].
   unfold EP, P1 in H3.
   simpl in H3; unfold O.eval_op in H3; simpl in H3.
   destruct H7; apply orb_prop in H6; destruct H6.
     generalize H3; clear H3.
     case (existsb (Gr.v_eqb u_) (m1 L) || existsb (Gr.v_eqb t_) (m1 L)); intro.
     rewrite H3; trivial.
     apply Gr_v_eqb_true in H6; rewrite <-H6.
     symmetry; apply Gr.remove_vertex_diff_1 with t_; trivial.
     auto.
     destruct H3; split.
     rewrite Gr.in_graph_edge_sym; trivial.
     intros x y Hin; decompose [and or] (H7 x y Hin); clear H7; subst; intuition.
     rewrite H6 in H3; simpl in H3; rewrite H3; trivial.
     generalize H3; clear H3.
     case (existsb (Gr.v_eqb u_) (m1 L) || existsb (Gr.v_eqb t_) (m1 L)); intro.
     rewrite H3; trivial.
     apply Gr_v_eqb_true in H6; rewrite <-H6.
     symmetry; apply Gr.remove_vertex_diff_1 with u_; trivial.
     auto.
     rewrite H6 in H3; rewrite orb_true_r in H3; rewrite H3; trivial.
   generalize H9; unfold EP1; expr_simpl; mem_upd_simpl.
   intro Heq; apply nat_eqb_true in Heq.
   rewrite Gr.remove_vertex_size; [ | trivial].
   rewrite Heq.
   replace (pred (n - m1 i))%nat with (n - (m1 i + 1))%nat by omega.
   apply nat_eqb_refl.
   generalize H4; clear H4; expr_simpl; intro Heq.
   apply nat_eqb_true in Heq; rewrite Heq, plus_comm; apply nat_eqb_refl.

 Close Scope bool_scope.
 (* 3rd proof obligation of while rule *)
 intro j.
 apply equiv_cons with (Q:=req_mem_rel (Vset.singleton v)
   ((I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j)) /-\ EP1 P1) /-\ EP1 (v \in G)).

 apply equiv_strengthen_range.
   apply decMR_req_mem_rel; refine (decMR_and 
     (decMR_and I'_dec (decMR_and _ _)) _); auto.

 intros k m1 m2 [ [ [_ [_ [_ ?] ] ] [? ?] ] ?] f Hf.
 rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
 simpl DE.eval_support.
 
 apply US.weighted_choice_in_graph.
 apply leb_complete; change (S (m1 i)) with (1 + m1 i)%nat; rewrite plus_comm;
  trivial.
 apply nat_eqb_true; trivial.
 intros; rewrite deno_nil_elim.
 apply Hf; expr_simpl.
 
 eapply equiv_sub; 
  [ | | apply equiv_random with 
   (Q:=req_mem_rel (Vset.singleton v)
    ((I' /-\ EP1 (i <! n) /-\ EP1 (i =?= j)) /-\ EP1 P1))].
 unfold eq_support, andR, I', req_mem_rel, kreq_mem, andR, EP, EP1.
 intros.
 decompose [and] H; clear H.
 split.
 rewrite H1 in H2.
 simpl; rewrite H2, H0; trivial.

 unfold forall_random; intros; expr_simpl; mem_upd_simpl.
 repeat split; trivial.
 intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl.
 intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl.
 apply H0; trivial.
 apply H0; trivial.

 unfold req_mem_rel, req_mem, andR; intuition.

 apply equiv_sub with 
 (P:= req_mem_rel (Vset.singleton v) 
  ((I' /-\ EP1 (v \in G) /-\ EP1 (i <! n) /-\ EP1 (i =?= j)) /-\ EP1 P1)) 
 (Q:= req_mem_rel {{ i, G, L, v}}  ((I' /-\ EP1 (i =?= S j)) /-\ EP1 P1)).
 unfold I', req_mem_rel, andR; intros; decompose [and] H;  repeat split; intuition.
 unfold I', req_mem_rel, kreq_mem, andR; intuition.
 eqobsrel_tail; unfold implMR, I', req_mem_rel, andR;
   simpl; unfold O.eval_op; simpl; repeat split; intuition; mem_upd_simpl.
 unfold EP1, EP in *; rewrite H2 in H3.
 assert  (kreq_mem {{ i, G, L, v}} m1 m2).
 intros ? ? Hin; Vset_mem_inversion Hin; subst; auto.
 apply req_mem_weaken with (2:=H6); vm_compute; trivial.
 intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl; auto.
 rewrite (H _ i); trivial.
 rewrite (H _ L), (H0 _ v); trivial.

 unfold EP1, EP in *; rewrite H2 in H3; rewrite H3, H0.
 apply Gr.in_graph_remove_vertex; auto.
 
 trivial.

 generalize H6; mem_upd_simpl; clear H6; intro.
 generalize (Gr.v_eqb_spec (m1 v) x); destruct (Gr.v_eqb (m1 v) x); intro.
 subst.
 apply Gr.edge_vertex in H6; destruct H6.
 contradict H6; rewrite (H0 _ v); trivial; apply Gr.remove_vertex_eq.
 
 generalize (Gr.v_eqb_spec (m1 v) y); destruct (Gr.v_eqb (m1 v) y); intro. 
 subst.
 apply Gr.edge_vertex in H6; destruct H6.
 contradict H11; rewrite (H0 _ v); trivial; apply Gr.remove_vertex_eq.

 apply Gr.in_graph_remove_edge_neq; trivial.
 apply H8.
 apply Gr.in_graph_remove_edge_conv in H6; trivial.

 unfold EP, P1; expr_simpl; mem_upd_simpl.
 unfold EP1 in H2; unfold EP in H3; rewrite H2 in H3.
 rewrite H3, H0; trivial.
 simpl in H2; unfold O.eval_op in H2; simpl in H2.
 apply orb_prop in H2; destruct H2; simpl; rewrite H2.
 rewrite orb_true_r; simpl; trivial.
 rewrite orb_true_r, orb_true_r; simpl; trivial.

 generalize H9; clear H9; unfold EP1; expr_simpl; mem_upd_simpl; intro Heq.
 rewrite Gr.remove_vertex_size; [ | trivial].
 apply nat_eqb_true in Heq.
 rewrite Heq.
 replace (pred (n - m1 i))%nat with (n - (m1 i + 1))%nat by omega.
 apply nat_eqb_refl.

 unfold EP1 in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
 apply nat_eqb_true in H7; rewrite H7; rewrite plus_comm; apply nat_eqb_refl.
 
 unfold EP1, P1 in H2; simpl in H2; unfold O.eval_op in H2; simpl in H2.
 apply orb_prop in H2; destruct H2; rewrite H2.
 rewrite orb_true_r; simpl; trivial.
 rewrite orb_true_r, orb_true_r; simpl; trivial.

 (* 4th proof obligation of while rule: Property Stability *)
 apply stability. 
 apply stability.

 (* 5th proof obligation of while rule: Termination *)
 intros k m1 m2 _; split; refine (ford_eq_intro _); apply loop_sem.
Qed.



(*  We bound [ Pr [c(G1)=L] / Pr [c(G2)=L] ] whenever
   G1 = G2 + {(t,u)} or G2 = G1 + {(t,u)} *)
Lemma lam_bound: (lam 0 <= exp eps)%R.
Proof.
 unfold lam, lam1, lam2, w; rewrite Rmult_1_r.
 generalize n_pos; destruct n; [intro; exfalso; omega | intros _].
 rewrite ProdRR_exp.
 apply exp_monotonic.
 transitivity 
  (sum_f_R0 (fun k => (sqrt (INR (S n0 - k)) / INR (S n0 - k)) * 
   (/ (2 * sqrt (INR (S n0)))) * eps)%R n0).
 apply sum_Rle; intros; unfold w.
 rewrite sqrt_div; 
  [ | apply Rlt_le; apply lt_0_INR; omega | apply lt_0_INR; omega]. 
 destruct (lt_dec n1 (S n0)); [ | exfalso; omega].
 apply Req_le; field.
 repeat split.
 apply not_eq_sym, Rlt_not_eq, sqrt_lt_R0, lt_0_INR; omega.
 apply not_eq_sym, Rlt_not_eq, lt_0_INR; omega.
 apply not_eq_sym, Rlt_not_eq, sqrt_lt_R0, lt_0_INR; omega.
 apply not_eq_sym, Rlt_not_eq, eps_pos.
 rewrite <-scal_sum.
 rewrite <-(Rmult_1_r eps) at 2.
 apply Rmult_le_compat; trivial.
 apply Rlt_le, eps_pos.
 apply sum_pos; intros; apply Rdiv_pos.
 apply Rdiv_pos.
 apply Rlt_le, sqrt_lt_R0, lt_0_INR; omega.
 apply lt_0_INR; omega.
 rewrite <-(Rmult_0_l 0).
 apply Rmult_le_0_lt_compat; trivial.
 fourier.
 apply sqrt_lt_R0, lt_0_INR; omega.

 rewrite <-scal_sum.
 apply Rmult_le_reg_l with (2 * sqrt (INR (S n0)))%R.
 rewrite <-(Rmult_0_l 0).
 apply Rmult_le_0_lt_compat; trivial.
 fourier.
 apply sqrt_lt_R0, lt_0_INR; omega.
 rewrite <-Rmult_assoc, Rinv_r_simpl_r.
 rewrite Rmult_1_r.

 transitivity (sum_f_R0 (fun k => / sqrt (INR (S n0 - k)))%R n0).
   apply sum_Rle; intros.
   rewrite <-(sqrt_square (INR (S n0 - n1))) at 2.
   rewrite sqrt_mult.
   apply Req_le; field.
   apply not_eq_sym, Rlt_not_eq, sqrt_lt_R0, lt_0_INR; omega.
   apply Rlt_le, lt_0_INR; omega.
   apply Rlt_le, lt_0_INR; omega.
   apply Rlt_le, lt_0_INR; omega.

 transitivity (sum_f_R0 (fun k => (/ sqrt (INR (S k)))%R) n0).
   apply Rfourier_eqLR_to_le.
   induction n0.
     simpl; trivial.
     rewrite decomp_sum, <-minus_n_O, <-pred_Sn; [ | apply lt_0_Sn ].
     rewrite sum_eq with (Bn:=fun i => (/ sqrt (INR (S n0 - i)))%R); trivial.
     rewrite IHn0, Rplus_comm; trivial.

 apply sum_inv_sqrt.

 apply not_eq_sym, Rlt_not_eq.
 rewrite <-(Rmult_0_l 0).
 apply Rmult_le_0_lt_compat; trivial;
  [fourier | apply sqrt_lt_R0, lt_0_INR; omega].
Qed.

Lemma lam'_bound: (lam' 0 <= exp eps)%R.
Proof.
 unfold lam', lam1', lam2'.
 replace (ProdRR (fun _ : nat => 1%R) 0 n) with 1%R.

 rewrite (proj2 (Rmult_ne _)); apply exp_monotonic.
 pattern eps at 2; replace eps with (eps / 1)%R by field.
 apply Rdiv_le; [ fourier | fourier | ].
 apply Rfourier_le; [ fourier | trivial ].

 symmetry; induction n. 
   simpl; trivial.
   rewrite ProdRR_S, IHn0; field.
Qed.

Hypothesis One_extra_edge_dec: decMR (fun k (m1 m2:Mem.t k) => 
 One_extra_edge (m1 G) (m2 G) t_ u_).

Theorem differential_privacy: 
  eequiva Pre E c E c Post (fun _ => exp eps) (fun _ => 0).
Proof.
 apply eequiva_case with 
   (fun k (m1 m2:Mem.t k) => One_extra_edge (m1 G) (m2 G) t_ u_).
   apply One_extra_edge_dec.
  apply eequiva_weaken with (P':= Pre1) (Q':=Post)
   (lam':= fun _ => lam 0) (ep' := fun _ => 0); trivial.
   unfold implMR, andR, Pre, Pre1, One_extra_edge; 
     intuition; auto using Gr.size_eq.
   intros; apply lam_bound.
 apply diff_private.
 apply eequiva_weaken with (P':= Pre2) (Q':=Post)
   (lam':= fun _ => lam' 0) (ep' := fun _ => 0); trivial.
   unfold implMR, andR, notR, Pre, Pre2, One_extra_edge; 
     intuition; auto using Gr.size_eq.
   intros; apply lam'_bound.
 apply diff_private'.
Qed.



    


  

