Require Export BuildTac.
Require Import Arith Even Div2.
Require Import DiscrProp.


Open Local Scope nat_scope.


(* *********************************************************************** *)
(*                        FRAGMENT OF ALEA LIBRARY v.7                     *)
(*                      to deal with series permutation                    *)
(* *********************************************************************** *)

(** Decidability *)
Lemma dec_sig_lt : forall P : nat -> Prop, (forall x, {P x}+{ ~ P x})
  -> forall n, {i | i < n /\ P i}+{forall i, i < n -> ~ P i}.
intros P Pdec.
induction n.
right; intros; exfalso; omega.
destruct IHn as [(i,(He1,He2))|Hn]; auto.
left; exists i; auto.
destruct (Pdec n) as [HP|HnP].
left; exists n; auto.
right; intros; assert (i < n \/ i = n) as [H1|H2]; subst; auto; try omega.
Defined.

Lemma dec_exists_lt : forall P : nat -> Prop, (forall x, {P x}+{ ~ P x})
  -> forall n, {exists i, i < n /\ P i}+{~ exists i, i < n /\ P i}.
intros P decP n; destruct (dec_sig_lt P decP n) as [(i,(H1,H2))|H].
left; exists i; auto.
right; intros (i,(H1,H2)); apply (H i H1 H2).
Save.

Definition eq_nat2_dec : forall p q : nat*nat, { p=q }+{~ p=q }.
intros (p1,p2) (q1,q2).
destruct (eq_nat_dec p1 q1) as [H1|H1]; subst.
destruct (eq_nat_dec p2 q2) as [H2|H2]; subst; auto with zarith.
right; intro Heq; apply H2.
injection Heq; trivial.
right; intro Heq; apply H1.
injection Heq; trivial.
Defined.

Definition fun_cte n (a:U) : nat -> U 
      := fun p => if eq_nat_dec p n then a else D0.

Lemma fun_cte_eq : forall n a, fun_cte n a n = a.
unfold fun_cte; intros; rewrite if_then; auto.
Save.

Lemma fun_cte_zero : forall n a p, p <> n -> fun_cte n a p = D0.
unfold fun_cte; intros; rewrite if_else; auto.
Save.

Lemma sigma_cte_eq : forall n a p, (n < p)%nat -> sigma (fun_cte n a) p == a.
induction 1.
rewrite sigma_S.
assert ((sigma (fun_cte n a)) n == 0).
apply sigma_zero.
intros k H; rewrite fun_cte_zero; auto; omega.
rewrite fun_cte_eq; rewrite H; auto.
rewrite sigma_S; rewrite IHle.
rewrite fun_cte_zero; auto; omega.
Save.

Hint Resolve sigma_cte_eq.

Lemma serie_cte_eq : forall n a, serie (fun_cte n a) == a.
intros; apply Ole_antisym; unfold serie.
apply lub_le.
intros p; destruct (le_lt_dec (S n) p) as [Hle|Hle].
rewrite sigma_cte_eq; auto.
transitivity (sigma (fun_cte n a) (S n)); auto. 
apply fmon_le_compat; auto with arith.
transitivity (sigma (fun_cte n a) (S n)); 
  [ | apply le_lub ].
rewrite sigma_cte_eq; auto.
Save.


Section PartialPermutationSerieLe.
Variables f g : nat -> U.

Variable s : nat -> nat -> Prop.
Hypothesis s_dec : forall i j, {s i j}+{~s i j}.

Hypothesis s_inj : forall i j k : nat, s i k -> s j k -> i = j.
Hypothesis s_dom : forall i, ~ f i == 0 -> exists j, s i j.

Hypothesis f_g_perm : forall i j, s i j -> f i == g j.

Lemma serie_perm_rel_le : (serie f <= serie g)%tord.
unfold serie at 1.
apply lub_le; intro n.
transitivity (serie (fun k => if dec_exists_lt _  
  (fun i => s_dec i k) n then g k else D0)).
induction n; auto.
rewrite sigma_S.
rewrite IHn; clear IHn.
apply (Ueq_orc (f n) 0); auto; intro H.
rewrite H; Usimpl; apply serie_le_compat; intro k.
destruct dec_exists_lt as [(i,(H1,H2))|H']; auto with zarith.
rewrite if_then; auto with zarith.
exists i; auto with zarith.
destruct (s_dom n) as (ni,Hni); auto.
rewrite <- (serie_cte_eq ni (f n)).
rewrite <- serie_plus.
apply serie_le_compat;intro k.
unfold fun_cte; destruct (eq_nat_dec k ni) as [Hkn|Hkn].
rewrite if_else; try omega.
rewrite if_then; try omega.
rewrite Hkn; auto.
exists n; subst; auto with zarith.
intros (i,(H1,H2)). 
subst; absurd (i=n); auto with zarith.
apply s_inj with ni; auto.
Usimpl; destruct dec_exists_lt as [(i,(H1,H2))|Hsknd]; auto.
rewrite if_then; auto.
exists i; auto with zarith.
apply serie_le_compat; intro k.
destruct dec_exists_lt as [(i,(H1,H2))|Hsknd]; auto.
Save.
End PartialPermutationSerieLe.

Section PartialPermutationSerieEq.
Variables f g : nat -> U.

Variable s : nat -> nat -> Prop.
Hypothesis s_dec : forall i j, {s i j}+{~s i j}.
Hypothesis s_fun : forall i j k : nat, s i j -> s i k -> j = k.
Hypothesis s_inj : forall i j k : nat, s i k -> s j k -> i = j.
Hypothesis s_surj : forall j, ~ g j == 0 ->  exists i, s i j.
Hypothesis s_dom : forall i, ~ f i == 0 -> exists j, s i j.
Hypothesis f_g_perm : forall i j, s i j -> f i == g j.

Lemma serie_perm_rel_eq : serie f == serie g.
apply Ole_antisym.
apply serie_perm_rel_le with s; auto.
apply serie_perm_rel_le with (fun i j => s j i); auto.
intros; apply s_fun with k; auto.
Save.
End PartialPermutationSerieEq.


Section PermutationSerie.
Variable s : nat -> nat.
Hypothesis s_inj : forall i j : nat, s i = s j -> i = j.
Hypothesis s_surj : forall j, exists i, s i = j.

Variable f : nat -> U.

Lemma serie_perm_le : (serie (fun i => f (s i)) <= serie f)%tord.
apply serie_perm_rel_le with (fun i j => s i = j); auto.
intros; apply (eq_nat_dec (s i) j).
intros; apply s_inj; transitivity k; auto.
intros; exists (s i); auto.
Save.

Lemma serie_perm_eq : serie f == serie (fun i => f (s i)).
apply serie_perm_rel_eq with (fun i j => s j = i); auto with zarith.
intros; apply (eq_nat_dec (s j) i).
intros; exists (s j); auto.
Save.

End PermutationSerie.
Hint Resolve serie_perm_eq serie_perm_le.




(* *********************************************************************** *)
(*                              AUXILIARY LEMMAS                           *)
(* *********************************************************************** *)

(* Open Scope positive_scope. *)
Open Scope Z_scope.
Open Scope R_scope.


Lemma sum_f_R0_eq_compat: 
  forall (An Bn : nat -> R) (N : nat),
  (forall n : nat, (n <= N)%nat -> An n = Bn n) ->
  sum_f_R0 An N = sum_f_R0 Bn N.
Proof.
 intros.
 apply Rle_antisym; apply sum_Rle;
   intros; rewrite H; trivial.
Qed.

Lemma Zeq_bool_comm: forall z1 z2, Zeq_bool z1 z2 = Zeq_bool z2 z1.
Proof.
 intros.
 case_eq (Zeq_bool z1 z2); intro Heq.
 symmetry; rewrite <-(@Zeq_is_eq_bool z2 z1); symmetry.
 apply (Zeq_bool_eq _ _ Heq).
 symmetry; apply not_true_iff_false; intro H'.
 apply ((Zeq_bool_neq _ _ Heq) (eq_sym (Zeq_bool_eq _ _ H'))).
Qed.

Lemma Zeq_bool_refl: forall z, Zeq_bool z z = true.
Proof.
 intro z.
 generalize (Zeq_bool_if z z); destruct (Zeq_bool z z).
   trivial.
   intro H.
   elim H; trivial.
Qed.

Lemma multRU_le_Rmult : forall (u1 u2:U) (x:R),
 (0 <= x)%R ->
 (iR u1 <= x * iR u2)%R -> 
 (u1 <= x ** u2)%tord.
Proof.
 intros u1 u2 x Hx H; unfold  multRU; repeat case_Rle.
 rewrite <-(retract_U u1); apply (iU_le H).
 elim n; apply Rmult_le_pos; auto.
 auto.
Qed.

Lemma has_ub_Rle_compat: forall f g,
  (forall k, (g k <= f k)%R) ->
  has_ub f ->
  has_ub g.
Proof.
 unfold has_ub, bound; intros f g Hfg (L,HL).
 exists L.
 apply Un_bound_imp. 
 intro n; rewrite (Hfg n).
 refine (HL _ (Un_in_EUn _ _)).
Qed.

Lemma sum_f_R0_le_compat: forall f g n,
 (forall (k:nat), (k <= n)%nat -> f k <= g k) ->
 sum_f_R0 f n <= sum_f_R0 g n.
Proof.
 intros.
 induction n; simpl.
   auto.
   rewrite IHn, H; auto with arith.
Qed.



Lemma Rdiv_gt_r_elim: forall (x y z:R),
  z > 0 ->
  x * z > y ->
  x > y / z.
Proof.
 intros x y z Hz H.
 rewrite <-(Rinv_r_simpl_l z x); 
   [ | intro H'; subst; apply (Rgt_irrefl _ Hz) ].
 apply (Rmult_gt_compat_r _ _ _ (Rinv_0_lt_compat _ Hz) H).
Qed.


Lemma Rmult_gt_r_elim: forall (x y z:R),
  z > 0 ->
  x > y / z ->
  x * z > y.
Proof.
 intros x y z Hz H.
 rewrite <-(Rinv_r_simpl_l z y); [ | apply (Rgt_not_eq _ _ Hz) ].
 rewrite Rmult_assoc, (Rmult_comm z), <-Rmult_assoc. 
 apply (Rmult_gt_compat_r _ _ _ Hz H).
Qed.


Lemma Rmult_gt_l_elim: forall (x y z:R),
  y > 0 ->
  x / y > z ->
  x > y * z.
Proof.
 intros x y z Hy H.
 rewrite <-(Rinv_r_simpl_r y x), Rmult_assoc;
   [ | intro H'; subst; apply (Rgt_irrefl _ Hy) ].
 apply (Rmult_lt_compat_l _ _ _ Hy).
 rewrite Rmult_comm; trivial.
Qed.

Lemma Rdiv_lt_r_elim: forall (x y z:R),
  z < 0 ->
  x * z > y ->
  x < y / z.
Proof.
 intros x y z Hz H.
 rewrite <-(Rinv_r_simpl_l z x); 
   [ | intro H'; subst; apply (Rgt_irrefl _ Hz) ].
 apply Ropp_lt_cancel.
 unfold Rdiv; rewrite <- 2 Ropp_mult_distr_r_reverse.
 refine (Rmult_lt_compat_r _ _ _ _ H). 
 apply (Ropp_0_gt_lt_contravar _ (Rinv_lt_0_compat _ Hz)).
Qed.

 


(* *********************************************************************** *)
(*                      (DISCRETE) NORMAL DISTRIBUTION                     *)
(* *********************************************************************** *)

Section NORMAL.  

 (* Scale factor *)
 Variable sf : R.
 Hypothesis sf_pos : 0 < sf.

 Variable ZeqU : Z -> Z -O-> U.
 Hypothesis cover_uR: forall (z:Z), cover (eq z) (ZeqU z).

 Definition pdf (ctr:Z) (z:Z) := 
  let t := IZR (z - ctr) in exp (- (Rsqr t) / sf).

 Axiom sigma_pdf_has_ub : forall ctr, 
  has_ub (sum_f_R0 (fun k => pdf ctr (iB k))).

 Lemma pdf_pos : forall ctr z, 0 <= pdf ctr z.
 Proof.
  intros; apply Rlt_le; apply exp_pos.
 Qed.

 Lemma pdf_notnul : forall a, exists b, 0 < pdf a b.
 Proof.
  intros; exists 0%Z; apply exp_pos.
 Qed.

 Lemma aux: forall (a:Z), has_ub (sum_f_R0 (fun k => pdf a (iB k))).
 Proof.
  intros; destruct (sigma_pdf_has_ub a) as [z Hz];
  exists z; intros ? [i Hi];
  rewrite Hi; apply Hz; exists i; auto.
 Qed.

 Definition Normal : Z -> Distr Z.
  intro a.
  refine (im_distr iB (exponential (fun a k => pdf a (iB k)) _ _ _ a)).
  exact (fun a' k' => pdf_pos a' (iB k')).
  intros; destruct (pdf_notnul a0) as [b Hb];
  exists (iN b); rewrite iB_N; trivial.
  exact aux.
 Defined.

 Lemma Normal_Discrete: forall (a:Z),
  is_Discrete (Normal a).
 Proof.
  unfold Normal, im_distr; intros.
  apply (is_Discrete_Mlet _ (exponential_is_Discrete _ _ _ _ _)).
  intros; apply is_Discrete_Munit.
 Qed.

 Lemma Normal_lossless: forall (a:Z),
   mu (Normal a) (fone _) == 1%U.
 Proof.
  intro a.
  unfold Normal; rewrite im_distr_simpl.
  apply exponential_lossless.
 Qed.

 Lemma Normal_point: forall (a z:Z), 
  mu (Normal a) (ZeqU z) ==
  iU (pdf  a z / sequence_ub 
    (sum_f_R0 (fun k => pdf a (iB k))) (aux a) 0).
 Proof.
  intros.
  unfold Normal; rewrite im_distr_simpl.
  match goal with  |- fmonot (mu ?d) ?f == _ => transitivity 
    (fmonot (mu d) (fun a' => B2U (nat_eqb a' (iN z))))
  end.
  apply mu_stable_eq; refine (ford_eq_intro _); intro k.
  unfold B2U; case_eq (nat_eqb k (iN z)); intro H1; 
    apply (cover_elim (cover_uR (iB k)) z); [ auto | | | auto | | ];
      intros (H2,H3); trivial.
      elim H2; rewrite (nat_eqb_true H1), iB_N; trivial.
      rewrite <-H2;  refine (cover_eq_one _  (cover_uR (iB k)) _); trivial.
      refine (cover_eq_zero _ (cover_uR _) _); auto.
      generalize (nat_eqb_spec k (iN z)); rewrite H1; clear H1; intro H1.
      elim H1; rewrite <-H2, iN_B; trivial.
  unfold exponential, B2U.
  rewrite discretize_point, iB_N.
  trivial.
 Qed.

 Lemma Normal_const_weight: forall a1 a2,
  sequence_ub (sum_f_R0 (fun k : nat => pdf a1 (iB k))) (aux a1) 0 =
  sequence_ub (sum_f_R0 (fun k : nat => pdf a2 (iB k))) (aux a2) 0.
 Proof.
  intros.
  assert (H:has_ub (sum_f_R0 (fun k : nat => pdf a2 (iB k + (a2 - a1))))).
    apply has_ub_Rle_compat with (sum_f_R0 (fun k => pdf a1 (iB k))).
    intros k; apply sum_f_R0_le_compat; intros.
    unfold pdf;  replace (iB k0 + (a2 - a1) - a2)%Z 
      with (iB k0 - a1)%Z; [ trivial | ring ].
    apply sigma_pdf_has_ub.
  transitivity (sequence_ub (sum_f_R0 (fun k => pdf a2 (iB k + (a2 - a1)))) H 0).
    apply Rlub_eq_compat; intro k.
    apply sum_f_R0_eq_compat; intros; unfold pdf.
    replace (iB n + (a2 - a1) - a2)%Z with (iB n - a1)%Z; [ trivial | ring ].
    symmetry; refine (series_f_shift _ _ _ _ (pdf_pos a2)).
 Qed.

 Lemma Normal_shift: forall (a:Z) f,
  mu (Normal a) f == mu (Normal 0) (fun z => f (z + a)%Z).
 Proof.
  intros; simpl.
  apply serie_perm_rel_eq with (s:= fun i j => (iB i - a)%Z  = iB j).
  intros; apply Z_eq_dec.
  intros i j j' Hj Hj'.
  rewrite <-(iN_B j), <-(iN_B j'), <-Hj, <-Hj'; trivial.
  intros i i' j  Hi Hi'.
  rewrite <-(iN_B i), <-(iN_B i').
  replace (iB i) with (iB j + a)%Z by omega.
  replace (iB i') with (iB j + a)%Z by omega.
  trivial.
  intros j _.
  exists (iN (iB j + a)%Z); rewrite iB_N; ring.
  intros j _.
  exists (iN (iB j - a)%Z); rewrite iB_N; ring.
  intros i j Hij.
  rewrite (Normal_const_weight a 0).
  unfold pdf; rewrite <-Hij,Zminus_0_r.
  rewrite Zplus_comm, Zplus_minus.
  trivial.
 Qed.

 Let Z_Gt := fun (L:R) (z:Z) => if Rlt_dec L (IZR z) then 1%U else D0.
 Let Z_Lt := fun (L:R) (z:Z) => if Rgt_dec L (IZR z) then 1%U else D0.

 Lemma Normal_dist_asym: forall (a1 a2:Z) delt (lam:R),
  1 <= lam ->
  let t:= IZR (a1-a2)%Z in
  let alpha := (sf * ln lam - Rsqr t) / (2 * t) in
  (t > 0 -> (mu (Normal 0) (Z_Gt alpha) <= delt)%tord) ->
  (t < 0 -> (mu (Normal 0) (Z_Lt alpha) <= delt)%tord) ->
  le_dist_asym (Normal a1) (Normal a2) lam delt.
 Proof.
  intros a1 a2 delt lam Hlam t alpha Hdelt1 Hdelt2.
  destruct (Req_EM_T t 0)  as [Heq | Hneq ].
  (* case [a1 = a2] *)
  unfold t in Heq.
  rewrite (Zminus_eq _ _ (eq_IZR_R0 _ Heq)).
  apply le_dist_asym_weaken_ep with D0;
    [ trivial | apply (le_dist_asym_nul _ Hlam) ].
  (* case [a1 <> a2] *)     
  intro f; unfold d_expr_asym.
  set (S := fun z => if Rle_dec (pdf a1 z) 
    (lam * pdf a2 z) then true else false).
  rewrite (mu_restr_split (Normal a1) S f),
    (mu_restr_split (Normal a2) S f).
  rewrite <-(multRU_distr_plus_l _ _ Hlam), 
    Uplus_minus_perm_assoc.
  rewrite <-(Uplus_zero_left delt); apply Uplus_le_compat;
    [ apply Uminus_le_zero | rewrite Uminus_le_left ].
  (* Multiplicative factor bound *)
  set (Ha1_discr := disc_eqpoint_l
    (Normal_Discrete a1) (Normal_Discrete a2)).
  set (Ha2_discr := disc_eqpoint_r
    (Normal_Discrete a1) (Normal_Discrete a2)).
  set (p:= parity_split (D_points (Normal_Discrete a1)) 
    (D_points (Normal_Discrete a2))); fold p in Ha1_discr, Ha2_discr.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr Ha1_discr)),
    (mu_is_Discrete _ cover_uR (mkDiscr Ha2_discr)); simpl.
  rewrite  (discr_distr_simpl _ cover_uR  Ha1_discr), 
    (discr_distr_simpl _ cover_uR  Ha2_discr).
  rewrite <-(multRU_serie _ Hlam).
  apply serie_le_compat; intro k.
  unfold restr, S; destruct (Rle_dec (pdf a1 (p k)) 
    (lam * pdf a2 (p k))) as [HS | _ ]; [ | repeat Usimpl; auto ].
  apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k);
    [auto | | ]; intros [_ H5]; rewrite H5; repeat Usimpl; [ | auto ].
  rewrite <-(Umult_multRU_assoc _ _ Hlam); apply Umult_le_compat_left.
  rewrite 2 Normal_point.
  apply multRU_le_Rmult; [ fourier | ].
  assert (Haux0: forall a,
    0 < sequence_ub (sum_f_R0 (fun k : nat => pdf a (iB k))) (aux a) 0).
      intro a; apply y_pos; [ intro; apply pdf_pos | destruct (pdf_notnul a)
        as [z' Hz']; exists (iN z'); rewrite iB_N; trivial ].
  assert (Haux1: forall a z,
   0 <= pdf a z / sequence_ub (sum_f_R0 (fun k => pdf a (iB k))) (aux a) 0 <= 1).
    intros a z; split.
      apply (Rdiv_pos (pdf_pos _ _) (Haux0 _)).
      apply (Rdiv_le_1 (Haux0 _)).
      rewrite <-(iB_N z).
      apply (serie_f_le (fun (a':Z) (k':nat) => pdf a' (iB k'))).
      intros; apply pdf_pos.
  rewrite 2 retract_R; try apply Haux1.
  rewrite (Normal_const_weight a1 a2).
  unfold Rdiv; rewrite <-Rmult_assoc.
  refine (Rmult_le_compat_r _ _ _ _ HS).
  refine (Rlt_le _ _ (Rinv_0_lt_compat _ (Haux0 _))).
  (* Additive term *)
  transitivity  (mu (Normal a1) (charfun (negP S))).
    apply mu_monotonic; apply restr_le_compat; auto.
  rewrite Normal_shift.
  destruct (Rdichotomy _ _ Hneq) as [Ht | Ht].
  (* case [a1 < a2] *)       
  transitivity  (mu (Normal 0) (Z_Lt alpha)).
    apply mu_monotonic; refine (ford_le_intro _); intro z.
    unfold charfun, restr, negP, S, negb, fone, Z_Lt.
    match goal with |- context [Rle_dec ?x ?y] => 
      destruct (Rle_dec x y) as [_ | H] end; trivial.
    match goal with |- context [Rgt_dec ?x ?y] => 
      destruct (Rgt_dec x y) as [_ | H'] end;
       [ trivial | elim H'; clear H' ].
    apply Rnot_le_lt in H.
    unfold alpha.
    apply Rdiv_lt_r_elim; [ fourier | ].
    cut (IZR z * (2 * t) +  Rsqr t > sf * ln lam); [ 
      generalize (IZR z * (2 * t)) (sf * ln lam); intros; fourier | ].
    apply (Rmult_gt_l_elim _ _ _ sf_pos).
    rewrite <-(ln_exp ((IZR z * (2 * t) + Rsqr t) / sf)).
    apply (ln_increasing); [ fourier | apply  Rfourier_gt_to_lt ].  
    replace (exp ((IZR z * (2 * t) + Rsqr t) / sf)) with
      (exp (- Rsqr (IZR z) / sf) * exp (Rsqr (IZR z + t) / sf)).
    Focus 2.
      rewrite <-exp_plus; apply f_equal.  
      unfold t; repeat rewrite minus_IZR.
      unfold Rdiv; rewrite <-Rmult_plus_distr_r; apply Rmult_eq_compat_r.
      rewrite Rsqr_plus, Rsqr_minus.
      generalize  (IZR z) (IZR a1) (IZR a2); intros z' a1' a2'; ring.
    apply (Rmult_gt_r_elim _ _ _ (exp_pos _)).
    unfold Rdiv at 2; rewrite <-exp_Ropp.
    revert H; unfold pdf, t.
    replace (z + a1 - a1)%Z with z by ring.
    rewrite <-plus_IZR; replace (z + (a1 - a2))%Z
      with (z + a1 - a2)%Z by omega.
    unfold Rdiv at 4; rewrite <-Ropp_mult_distr_l_reverse.
    trivial.
  exact (Hdelt2 Ht).
  (* case [a1 < a2] *)       
  transitivity  (mu (Normal 0) (Z_Gt alpha)).
    apply mu_monotonic; refine (ford_le_intro _); intro z.
    unfold charfun, restr, negP, S, negb, fone, Z_Gt.
    match goal with |- context [Rle_dec ?x ?y] => 
      destruct (Rle_dec x y) as [_ | H] end; trivial.
    match goal with |- context [Rlt_dec ?x ?y] => 
      destruct (Rlt_dec x y) as [_ | H'] end; 
       [ trivial | elim H'; clear H' ].
    apply Rnot_le_lt in H.
    unfold alpha.
    apply Rfourier_gt_to_lt.
     apply Rdiv_gt_r_elim; [ fourier | ].
    cut (IZR z * (2 * t) +  Rsqr t > sf * ln lam); [ 
      generalize (IZR z * (2 * t)) (sf * ln lam); intros; fourier | ].
    apply (Rmult_gt_l_elim _ _ _ sf_pos).
    rewrite <-(ln_exp ((IZR z * (2 * t) + Rsqr t) / sf)).
    apply (ln_increasing); [ fourier | apply  Rfourier_gt_to_lt ].  
    replace (exp ((IZR z * (2 * t) + Rsqr t) / sf)) with
      (exp (- Rsqr (IZR z) / sf) * exp (Rsqr (IZR z + t) / sf)).
    Focus 2.
      rewrite <-exp_plus; apply f_equal.  
      unfold t; repeat rewrite minus_IZR.
      unfold Rdiv; rewrite <-Rmult_plus_distr_r; apply Rmult_eq_compat_r.
      rewrite Rsqr_plus, Rsqr_minus.
      generalize  (IZR z) (IZR a1) (IZR a2); intros z' a1' a2'; ring.
    apply (Rmult_gt_r_elim _ _ _ (exp_pos _)).
    unfold Rdiv at 2; rewrite <-exp_Ropp.
    revert H; unfold pdf, t.
    replace (z + a1 - a1)%Z with z by ring.
    rewrite <-plus_IZR; replace (z + (a1 - a2))%Z
      with (z + a1 - a2)%Z by omega.
    unfold Rdiv at 4; rewrite <-Ropp_mult_distr_l_reverse.
    trivial.
  exact (Hdelt1 Ht).
 Qed.

 Lemma Normal_dist_aux: forall (a1 a2:Z) delt (lam:R),
  1 <= lam ->
  let t:= (IZR (a1-a2)%Z) in
  let alpha1 := (sf * ln lam - Rsqr t) / (2 *  Rabs t) in
  let alpha2 := (sf * ln lam - Rsqr t) / (2 * - Rabs t) in
  (mu (Normal 0) (Z_Gt alpha1) <= delt)%tord ->
  (mu (Normal 0) (Z_Lt alpha2) <= delt)%tord ->
  le_dist (Normal a1) (Normal a2) lam delt.
 Proof.
  intros a1 a2 delt lam Hlam t alpha1 alpha2 Hdelt1 Hdelt2.
  assert (Hcontr: forall (r:R), r > 0 -> r < 0 -> False) by
    (intros r H1 H2; apply (RIneq.Rle_not_lt 0 r (Rlt_le _ _ H2) H1)).
  destruct (Rtotal_order (IZR (a1-a2)%Z) 0) as [Ht | [Ht | Ht] ].
  (* case a1 < a2 *)
  apply (le_dist_le_dist_asym Hlam).
    refine (Normal_dist_asym _ _ _ _ Hlam _ _); fold t; intro Ht'.
      elim (Hcontr t Ht' Ht).
      pattern t at 2; rewrite <-(Ropp_involutive t), <-(Rabs_left t Ht).
      exact Hdelt2.
    refine (Normal_dist_asym _ _ _ _ Hlam _ _); fold t; intro Ht'.
      replace (a2 - a1)%Z with (-(a1 - a2))%Z by ring.
      rewrite Ropp_Ropp_IZR; rewrite <-(Rabs_left (IZR (a1 - a2)%Z) Ht) at 2.
      rewrite <-Rsqr_neg.
      exact Hdelt1.      
      elim (Hcontr t); trivial.
      apply Ropp_gt_cancel; rewrite Ropp_0; unfold t.
      replace (- IZR (a1 - a2)%Z) with (IZR (a2 - a1)%Z) by
        (rewrite <-opp_IZR; apply f_equal; ring).
      trivial.
  (* case a1 = a2 *)
  rewrite (Zminus_eq _ _ (eq_IZR_R0 _ Ht)).
  apply le_dist_weaken_ep with D0;
    [ trivial | apply (le_dist_nul _ Hlam) ].
  (* case a1 > a2 *)
  apply (le_dist_le_dist_asym Hlam).
    refine (Normal_dist_asym _ _ _ _ Hlam _ _); fold t; intro Ht'.
      rewrite <-(Rabs_right t (Rgt_ge _ _ Ht)) at 2.
      exact Hdelt1.
      elim (Hcontr t Ht Ht').
    refine (Normal_dist_asym _ _ _ _ Hlam _ _); intro Ht'.
      elim (Hcontr t); trivial.
      apply Ropp_gt_cancel; rewrite Ropp_0; unfold t.
      replace (- IZR (a1 - a2)%Z) with (IZR (a2 - a1)%Z) by
        (rewrite <-opp_IZR; apply f_equal; ring).
      trivial.
      replace (a2 - a1)%Z with (-(a1 - a2))%Z by ring.
      rewrite Ropp_Ropp_IZR; 
        rewrite <-(Rabs_right (IZR (a1 - a2)%Z) (Rgt_ge _ _ Ht)) at 2.
      rewrite <-Rsqr_neg.
      exact Hdelt2.      
 Qed.

 Lemma Normal_sym_bound: forall (a:R),
  mu (Normal 0) (Z_Gt a) == mu (Normal 0) (Z_Lt (-a)%R).
 Proof.
  intro a; simpl.
  apply serie_perm_rel_eq with (s:= fun i j => iB i  = (- iB j)%Z).
  intros; apply Z_eq_dec.
  intros i j j' Hj Hj'.
  rewrite <-(iN_B j), <-(iN_B j').  
  replace (iB j) with (- iB i)%Z by omega.
  replace (iB j') with (- iB i)%Z by omega.
  trivial.
  intros i i' j  Hi Hi'.
  rewrite <-(iN_B i), <-(iN_B i'), Hi, Hi'; trivial.
  intros j _.
  exists (iN (- iB j)%Z); rewrite iB_N; ring.
  intros j _.
  exists (iN (- iB j)%Z); rewrite iB_N; ring.
  intros i j Hij.
  apply Umult_eq_compat.
     rewrite Hij; unfold pdf.
     rewrite 2 Zminus_0_r, Ropp_Ropp_IZR, <-Rsqr_neg.
     trivial.
  unfold Z_Gt, Z_Lt.
  destruct (Rlt_dec a (IZR (iB i))) as [H1 | H1];
    destruct (Rgt_dec (- a) (IZR (iB j))) as [H2 | H2]; trivial.
  rewrite Hij in H1; elim H2; clear Hij H2.
  rewrite Ropp_Ropp_IZR in H1; fourier.
  rewrite Hij in H1; elim H1; clear Hij H1.
  rewrite Ropp_Ropp_IZR; fourier.
 Qed.

 Lemma Normal_dist: forall (a1 a2:Z) delt (lam:R),
  1 <= lam ->
  let t:= (IZR (a1-a2)%Z) in
  let alpha := (sf * ln lam - Rsqr t) / (2 *  Rabs t) in
  (mu (Normal 0) (Z_Gt alpha) <= delt)%tord ->
  le_dist (Normal a1) (Normal a2) lam delt.
 Proof.
  intros a1 a2 del lam Hlam t alpha H.
  destruct (Z_eq_dec a1 a2) as [Ha | Ha].
    (* a1 = a2 *)
    rewrite Ha.
    apply le_dist_weaken_ep with D0;
      [ trivial | apply (le_dist_nul _ Hlam) ].
    (* a1 <> a2 *)
    apply (Normal_dist_aux _ _ _ _ Hlam H).
    rewrite <-H, Normal_sym_bound.
    unfold alpha, Rdiv at 1.
    rewrite Ropp_mult_distr_r_reverse, <-Ropp_inv_permute,
      Ropp_mult_distr_r_reverse; trivial.
    apply Rmult_integral_contrapositive; 
       split; [ intros ?; fourier | ].
    refine (Rabs_no_R0 _ (not_0_IZR _ _)).
    intro H'; apply Ha; omega.
 Qed.

End NORMAL.




