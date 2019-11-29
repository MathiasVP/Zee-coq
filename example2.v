Require Import Autosubst.Autosubst.
Require Import Zee.lattice Zee.lang Zee.dec Zee.vals Zee.frame Zee.maplike Zee.sem Zee.typesystem.
Require Import Arith List Coq.Program.Basics Coq.Lists.ListSet Lia Coq.ZArith.BinInt.
Require Import Coq.Classes.RelationClasses.

Section Example2.
  Context {A : Set} {BinOpS : Set} `{lattice A}.
  Context {MINUS MULT : BinOpS}.
  Definition Lab := @Lab A.
  Definition Ty := @Ty A.
  Definition LabVar := @LabVar A.
  Definition SecTy := @SecTy A.
  Definition SecTyV := @SecTyV A.
  Definition AtomSecTy := @AtomSecTy A.
  Definition Cmd := @Cmd A BinOpS.
  Definition Expr := @Expr A BinOpS.
  Definition V := @V A.

  Context {δ : string -> option Z}.
  Context {F: string -> option (list (string * Lab) *
                               list (string * Lab) *
                               list (string * SecTy) * Lab * Lab * Cmd) }.
  Context {eval_binop: BinOpS -> V -> V -> V}.
  Context {type_binop: BinOpS -> SecTy -> SecTy -> SecTy -> Prop}.
  Context {VarT ArgT LocT MemT : Type}
          {H_var_finmaplike: FinMapLike VarT string (A + SecTyV)}
          {H_arg_finmaplike: FinMapLike ArgT string SecTyV}
          {H_loc_finmaplike: FinMapLike LocT string SecTyV}
          {H_mem_maplike: MapLike MemT nat V}.
  Definition Frame := @Frame A VarT ArgT LocT MemT _ _ _ _.
  Definition PFrame := @PFrame A VarT ArgT LocT _ _ _.
  Definition EFrame := @EFrame A MemT _.

  Notation "o ':' s1 ',' s2 '⤇' s" := (type_binop o s1 s2 s) (at level 70, s at next level).
 
  Definition Var := @Var A BinOpS.
  Definition Num := @Num A BinOpS.
  Hint Unfold Var Num.
  Coercion Var: string >-> lang.Expr.
  Coercion Num: nat >-> lang.Expr.
  Coercion STy: lang.Ty >-> Funclass.
  Coercion eval_binop : BinOpS >-> Funclass.
  
  Definition public_varty (x : string) := VarTy x ⊥.
  Coercion public_varty: string >-> lang.AtomSecTy.

  Coercion SPat : lang.Pat >-> Funclass.
  Coercion PVar: string >-> AtomPat.
  
  Definition program : Cmd :=
    UNPACKTY "α" AS TYPE ⊥, "x" AS "α" ::=
      TYPACK (IntTy ⊥, 42)
        AS ∃ ("α" ::: ⊥) "α" IN
      LET "y" AS (IntTy ⊥) ::= 0 IN
        MATCH "α" WITH
          (PProd "β" "γ", SKIP)
        | (PAtom (PInt "κ"), &("y") *= Num 1)
        ENDMATCH
      ENDLET
    ENDUNPACKTY.
  Hint Unfold program.

  Definition step_many := @step_many A BinOpS _ δ F eval_binop _ _ _ _ _ _ _ _.
  Notation "cfg1 '-->[' n ']' cfg2" := (step_many cfg1 cfg2 n) (at level 80).
  Notation "cfg1 '-->*' cfg2" := (exists n, cfg1 -->[n] cfg2) (at level 80).

  Definition wt := @wt A BinOpS _ F type_binop.
  Notation "'[' Γ ',' Π ',' ϕ ',' pc ',' fr ']' '⊢' c" := (wt Γ Π ϕ pc fr c) (at level 70, c at next level).

  Lemma program_is_wt:
    [∅, ∅, nil, ⊥, ⊥] ⊢ program.
  Proof.
    unfold program.
    eapply WtUnpTy.
    - eapply wt_packty.
      + eapply eq_rewrite4_Proper.
        * eapply MorphismUR_wt_sectype.
        * rewrite <- idem_join.
          reflexivity.
        * do 2 constructor; constructor.
      + do 2 constructor.
        * reflexivity.
        * constructor.
      + eapply wt_sub.
        * constructor.
        * cbn.
          eapply sub_atom.
          constructor.
          unfold flowsto_with.
          intros.
          reflexivity.
    - do 2 constructor.
      rewrite -> idem_join.
      reflexivity.
    - constructor.
      constructor.
      + reflexivity.
      + constructor.
    - eapply WtLet.
      + constructor.
      + do 2 constructor; constructor.
      + do 2 constructor.
        rewrite -> idem_join.
        reflexivity.
      + repeat rewrite -> idem_join.
        reflexivity.
      + eapply WtMatch.
        * reflexivity.
        * reflexivity.
        * intros.
          destruct i.
          {
            cbn in H.
            inversion H; subst; clear H.
            rewrite -> subst_secty_cmd_skip.
            constructor.
          }
          {
            destruct i.
            - cbn in H.
              inversion H; subst; clear H.
              rewrite -> subst_secty_cmd_write.
              rewrite -> subst_secty_expr_addrof.
              unfold Num.
              rewrite -> subst_secty_expr_num.
              eapply WtWrite.
              + constructor.
                reflexivity.
              + constructor.
              + cbn.
                constructor.
                constructor.
                unfold flowsto_with.
                intros.
                intro.
                cbn.
                rewrite -> join_bot.
                eapply idem_join.
            - cbn in H.
              eapply nth_error_In in H.
              firstorder.
          }
  Qed.
          
  Goal
    exists stk q,
      δ "x" = Some 0%Z ->
      δ "y" = Some 1%Z ->
      ⟨program, initial_stk program, 0, 0⟩ -->* ⟨CStop, stk, q, 0⟩ /\
      stk ? 1 + fp_of (initial_stk program) = Some (VNum 1).
  Proof.
    do 2 eexists.
    intros.
    split.
    {
      eexists.
      unfold program.
      eapply StepManyS.
      - constructor.
        + constructor.
          * constructor; repeat constructor.
          * constructor.
        + simpl.
          constructor. constructor.
          * simpl.
            solve_mapsto.
          * constructor.
        + eassumption.
      - cbn. eapply StepManyS.
        + step_seq.
          step_let.
          intro; discriminate.
        + cbn.
          eapply StepManyS.
          * repeat step_seq; try discriminate.
            -- step_match.
            -- intro; discriminate.
          * cbn. eapply StepManyS.
            repeat step_seq; try discriminate.
            -- cbn.
               step_write.
            -- eapply StepManyS.
               step_seq.
               constructor.
               cbn. eapply StepManyS. constructor. eapply StepMany0.
    }
    {
      simpl_mapsto.
      reflexivity.
    }
  Qed.

End Example2.