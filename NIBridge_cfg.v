(* An aborted attempt to have a generalized formulatio for Bridge NI *)

Definition NI_idx_cfg (n: nat) : Prop :=
  forall Γ pc c,
    -{ Γ, pc ⊢ c }- ->
    forall ev1 ev2 cfg_m cfg_s cfg_m' cfg_s' n',
      c = cmd_of cfg_m ->
      config_low_eq Γ cfg_m cfg_s ->
      cfg_m ⇨+/(SL, Γ, ev1, n ) cfg_m' ->
      cfg_s ⇨+/(SL, Γ, ev2, S n') cfg_s' ->
      config_low_eq Γ cfg_m' cfg_s' /\
      event_low_eq Γ ev1 ev2.

Theorem ni_bridge_cfg :
  forall n, NI_idx_cfg (S n).
Proof.
  apply strongind.
  (* Base case *)
  {
    unfold NI_idx_cfg.
    intros Γ pc c H; subst.
    cmd_has_type_cases (induction H) Case;
      intros ev1 ev2 [c_m m] [c_s s] [c_end m_end] [d_end s_end] n' H_cmd cfg_leq H_m H'_s.
    
    Case "T_Skip".
    {
      unfolds cmd_of; subst; unfolds* config_low_eq; destruct cfg_leq; subst.

      
      forwards H_a: skip_bridge_properties H_m.
      forwards H_b: skip_bridge_properties H'_s.
      destructs H_a.
      destructs H_b.
      subst.
      splits *.
    }
    Case "T_Assign".
    {
      unfolds cmd_of; subst; unfolds* config_low_eq; destruct cfg_leq; subst.
      
      repeat
        (match goal with
             | [ H: context [bridge_step_num] |- _ ] =>
               (apply assign_bridge_properties in H; repeat (super_destruct; subst))
             |  [ H: Γ x = Some ?U, H' : Γ x = Some ?V |- _ ] =>
                (assert (U = V) by congruence; subst; clear H)
         end).
      
      (* use NI for expressions *)
      forwards* low_eq: ni_exp.
      match goal with
          [ _ : Γ x = Some ?ℓ' |- _ ] =>
          (forwards* LE : low_eq_flowsto __ ℓ' low_eq;
           clear low_eq;
           rename ℓ' into ℓ_x)
      end.
      forwards* st_eq: leq_updates.
      splits *.
      (* take care of the remaining goal *)
      assert (Low ⊑ Low) by auto;
        assert ( ~ High ⊑ Low) by  (unfold not; intros H''; inversion H'');
        destruct ℓ_x; inverts* LE; 
        repeat specialize_gens.
    }
    (* TODO: move this elsewhere *)
    Ltac compare_stops:=
            match goal with
            [ _ : context[?C = STOP],  _ : context [?C <> STOP] |- _  ] =>
            (compare C STOP; intros; repeat specialize_gens)
            end.
    
    Case "T_Seq".
    {
      clear IHcmd_has_type2.
      unfold cmd_of in H_cmd; subst.
      unfold config_low_eq in cfg_leq.
      destruct cfg_leq as [cmd_eq leq]; subst.
      apply seq_comp_bridge_property in H_m.
      apply seq_comp_bridge_property in H'_s.

      super_destruct; (try (solve [omega])).
      (* the destruct above yields 4 cases, the two are automatically 
         taken care by omega; of the remaning two only one is possible; 
         we consider them here  *)
      
      - (* the only possible event *)
        forwards* (cfg_leq' & ev_leq):  IHcmd_has_type1 〈c1, m 〉 〈c1, s 〉.
        inverts* cfg_leq'.
        compare_stops.

      - (* impossible after applying the IH becase ev1 <> EmptyEvent *)
        forwards* (cfg_leq' & ev_leq) : IHcmd_has_type1 〈c1, m 〉.
        unfold event_low_eq in ev_leq.
        super_destruct.
        specialize_gens.
        match goal with [ H : low_event _ _ EmptyEvent |- _ ] => inversion H end.
    }
    
    (* neither if or while are possible in base case
       we use the following auxiliary ltac to discharge the goals *)

    Ltac discharge_if_while_base H :=
      bridge_num_cases (inversion H) SCase; subst;
      repeat match goal with
        | [ H : context [low_event_step] |- _ ] => invert_low_steps
        | [ H : context [high_event_step] |- _] => (invert_high_steps; subst)
        | [ H: context [is_stop] |-  _ ] => (do 2 unfolds in H; inverts*  H)
        | [ H : 〈 _, _  〉 = 〈STOP, _ 〉 |- _] => (inversion H ; contradiction)
        | [ H : 0 >= 1 |- _ ] => omega
      end.
    Case "T_if".
    {
      unfolds cmd_of; subst; unfolds* config_low_eq; destruct cfg_leq; subst.
      discharge_if_while_base H_m.
    }
    Case "T_While".
    {
      unfolds cmd_of; subst; unfolds* config_low_eq; destruct cfg_leq; subst.
      discharge_if_while_base H_m.
    }
  }
  (* inductive case *)
  {
    intros.
    unfold NI_idx_cfg.
    intros Γ pc c H_wt.

    cmd_has_type_cases (induction H_wt) Case;
      intros ev1 ev2 [c_m m] [c_s s] [c_end m_end] [d_end s_end] n' H_cmd cfg_leq H_m H'_s.
    Case "T_Skip".
    {
      (* impossible *)
      unfolds cmd_of; subst; unfolds* config_low_eq; destruct cfg_leq; subst.
      inversion H_m.
      invert_high_steps.
      intros.
      stop_contradiction_alt.
    }
    Case "T_Assign".
    { (* impossible *)
      unfolds cmd_of; subst; unfolds* config_low_eq; destruct cfg_leq; subst.
      inversion H_m.
      invert_high_steps.
      intros.
      stop_contradiction_alt.
    }
    Case "T_Seq".
    {
      unfold cmd_of in H_cmd; subst.
      unfold config_low_eq in cfg_leq.
      destruct cfg_leq as [cmd_eq leq]; subst.
      apply seq_comp_bridge_property in H_m.
      apply seq_comp_bridge_property in H'_s.

      super_destruct. (* we get four cases; only one is possible *)
      - (* impossible - show by appling the inner IH *)
        forwards* (cfg_leq' & ev_leq'): IHH_wt1 〈c1, m 〉.
        lets (A & B) : cfg_leq'.
        split~ .
        substs.
        compare_stops.
      - (* impossible - show by appling the outer IH *)
        unfold NI_idx_cfg in H.

        
        do 2 match goal with
          | [ H: context [?X < S ?n] |- _ ]=>
            assert (X <= n) by omega; clear H
          | [ H_m : 〈c1, ?m 〉 ⇨+/(SL, ?Γ , ?ev1, S ?X) 〈?C1, ?M 〉,               
                         X_le : context [ ?X <= _ ] |- _  ]
            =>
            (specializes H  X_le  pc c1); eauto
        end.
        specializes* H;eauto.
        lets (cfg_leq' & ev_eq') : H.
        lets (A&B): cfg_leq'.
        lets (X&Y): ev_eq'. subst.
        destruct X.
        specialize_gen.
        invert_low_event.
      - (* impossible - show by appling the inner IH *)
        forwards* (cfg_leq' & ev_leq') : IHH_wt1 〈c1, m 〉.
        lets (A & B): cfg_leq'.
        substs.
        lets (X & Y): ev_leq'.
        repeat specialize_gens.
        match goal with [ H: low_event _ Low EmptyEvent |- _ ] => inverts H end.
      - 
