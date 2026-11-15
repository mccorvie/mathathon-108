"""COMPUTED exact integration of stated draft band certificates.

The analytic/constant endpoints are inherited from W E706 and retain
their written-proof dependencies. No floating value is used to accept
a bound. This script proves no missing prime-band estimate.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json
HERE=Path(__file__).resolve().parent
alpha=Q(3,40);eta=Q(37,40)
C_lower=-Q(523707,250000);analytic_lower=-Q(693,500)
known_outer_q2=Q(24353,14400)
def I(a,b,l,u):return a*(u-l)+b*(u*u-l*l)/2
def H(l,u):
    if u<=alpha:return 7*eta*(u-l)
    if l>=alpha:return I(7,-7,l,u)
    return H(l,alpha)+H(alpha,u)
def band(l,u,a,b,name):
    return dict(name=name,left=l,right=u,density_a=a,density_b=b,
        contribution=I(a,b,l,u),H0_share=H(l,u),surplus=I(a,b,l,u)-H(l,u))
def scenario(cut,include_q5=False,include_nine=False,include_q6=False,include_mixed=False,include_mixed_q4=False,mixed_q4_index=53,include_seven_eight=False,sharp_q3=False,sharp_q4=False,include_q7_strip=False,include_low_seven=False,include_q3_alias=False,include_lower_q5=False,include_lower_q6=False,include_full_q7=False,include_integral_q4=False,include_middle_q5=False,include_typea_q7_right=False,include_typea_q7_left=False,include_middle_q6=False,include_folded_q5=False,include_compressed_q4=False,include_crt_q5=False,include_upper_q5=False,include_compressed_q6=False,include_crt_q4=False,include_crt_q6=False,include_middle_q7=False,include_upperstrip_q4=False,include_collision_lower_q6=False,include_smallcore_q8=False,include_collision_upper_q6=False,include_largeT_q8=False,include_Rlarge_upper_q8=False,include_Rlarge_partial_q8=False,include_E16_unit_q8=False):
    q4_loss=2+7*mixed_q4_index
    q4_cut=(5*alpha+q4_loss*(1+2*alpha))/(7+5*q4_loss)
    rows=[band(cut,Q(49,160),Q(53,8),0,'q3 full reference'),
          band(Q(49,160),Q(37,120),Q(3587,20),-564,'q3 protected bridge'),
          band(Q(37,120),Q(13,40),Q(347,20),-35,'q3 upper projected'),
          band(Q(13,40),Q(1,3),Q(321,20),-31,'q3 upper unprojected'),
          band(Q(37,160),Q(49,200),Q(151,20),-4,'q4 full reference'),
          band(Q(49,200),Q(1,4),Q(347,20),-44,'q4 protected top')]
    if include_q5:
        rows.append(band(Q(23,120),Q(1,5),Q(293,40),-4,'q5 unit secondary'))
    if include_nine:
        rows.append(band(Q(23,100),Q(37,160),Q(53,8),0,'q4 ordinary nine extension'))
    if include_q6:
        rows.append(band(Q(23,140),Q(1,6),Q(293,40),-5,'q6 unit secondary'))
    if include_mixed and not sharp_q3:
        assert cut==Q(23,80)
        rows.append(band(Q(2,7),cut,-Q(8521,40),764,'q3 mixed tertiary bounded index'))
    if include_mixed_q4 and not sharp_q4:
        rows.append(band(q4_cut,Q(23,100),Q(53,8)-q4_loss*Q(23,20),5*q4_loss,f'q4 mixed tertiary index factor {mixed_q4_index}'))
    if include_seven_eight and not sharp_q3:
        assert include_mixed
        rows.append(band(Q(10089,35320),Q(2,7),-Q(9809,40),876,'q3 seven/eight-node index factor 31'))
    if sharp_q3:
        assert cut==Q(23,80)
        rows.append(band(Q(43,160),cut,Q(173,40),8,'q3 actual two-form tertiary index at most 1'))
    if sharp_q4:
        rows.append(band(Q(9,40),Q(23,100),Q(173,40),10,'q4 actual two-form tertiary index at most 1'))
    if include_q7_strip and not include_full_q7:
        rows.append(band(Q(18579,138280),Q(43,320),7,-7,'q7 filtered-core H0 substrip'))
    if include_full_q7:
        assert include_q7_strip
        rows.append(band(Q(37,280),Q(43,320),Q(1,40),48,'q7 full A=0 canonical unit base'))
    if include_low_seven:
        assert sharp_q3
        rows.append(band(Q(13,50),Q(43,160),-Q(21,20),28,'q3 low-seven fourth form'))
    if include_q3_alias:
        assert include_low_seven
        rows.append(band(Q(1,4),Q(13,50),Q(187,20),-12,'q3 retained full central alias'))
    if include_lower_q5:
        assert include_q5
        rows.extend([band(Q(37,200),Q(13,70),Q(59,8),-6,'q5 lower fourth form, first branch'),
                     band(Q(13,70),Q(23,120),-Q(121,40),50,'q5 lower fourth form, second branch')])
    if include_lower_q6:
        assert include_q6
        rows.extend([band(Q(37,240),Q(13,80),Q(59,8),-6,'q6 lower fourth form, first branch'),
                     band(Q(13,80),Q(23,140),-Q(121,40),58,'q6 lower fourth form, second branch')])
    if include_integral_q4:
        assert sharp_q4
        rows.append(band(Q(13,60),Q(9,40),Q(101,40),18,'q4 whole strict integral next form'))
    if include_middle_q5:
        assert include_lower_q5
        rows.append(band(Q(2,11),Q(37,200),Q(517,40),-36,'q5 middle ordinary10/11 next form'))
    if include_typea_q7_right:
        assert include_full_q7
        rows.append(band(Q(49,360),Q(1,7),Q(53,8),-1,'q7 type-A-present right unit Gram'))
    if include_typea_q7_left:
        assert include_typea_q7_right
        rows.append(band(Q(43,320),Q(49,360),-Q(127,40),71,'q7 type-A-present left dual higher form'))
    if include_middle_q6:
        assert include_lower_q6
        rows.append(band(Q(43,280),Q(37,240),Q(517,40),-42,'q6 middle ordinary12/13/14 next form'))
    if include_folded_q5:
        assert include_middle_q5
        rows.append(band(Q(43,240),Q(2,11),Q(517,40),-36,'q5 folded ordinary11/12 next form'))
    if include_compressed_q4:
        assert include_integral_q4
        rows.append(band(Q(49,240),Q(43,200),Q(151,20),-5,'q4 retained-trace projector'))
    if include_crt_q5:
        assert include_folded_q5
        rows.append(band(Q(1,6),Q(7,40),Q(253,40),1,'q5 lower CRT bad11 unit'))
    if include_upper_q5:
        assert include_crt_q5
        rows.append(band(Q(7,40),Q(43,240),Q(151,20),-6,'q5 upper low11 projector'))
    if include_compressed_q6:
        assert include_middle_q6
        rows.append(band(Q(49,320),Q(43,280),Q(151,20),-7,'q6 upper low13 projector'))
    if include_crt_q4:
        assert include_compressed_q4
        rows.append(band(Q(1,5),Q(49,240),Q(253,40),1,'q4 lower CRT bad9 unit'))
    if include_crt_q6:
        assert include_compressed_q6
        rows.append(band(Q(3,20),Q(49,320),Q(253,40),1,'q6 lower CRT bad13 unit'))
    if include_middle_q7:
        assert include_typea_q7_left
        rows.extend([band(Q(1,8),Q(23,180),Q(45,8),7,'q7 middle source-zero lower'),
                     band(Q(23,180),Q(13,100),Q(639,40),-74,'q7 middle low-polynomial alias'),
                     band(Q(13,100),Q(37,280),Q(223,40),6,'q7 middle zero-first-form')])
    if include_upperstrip_q4:
        assert include_compressed_q4 and include_integral_q4
        rows.append(band(Q(43,200),Q(13,60),Q(517,40),-30,'q4 upper mass-quotient projector'))
    if include_collision_lower_q6:
        assert include_crt_q6
        rows.append(band(Q(1,7),Q(23,160),Q(45,8),6,'q6 collision source-zero lower'))
    if include_smallcore_q8:
        rows.append(band(Q(43,360),Q(23,190),Q(27,5),9,'q8 small-core p15 actual'))
    if include_collision_upper_q6:
        assert include_collision_lower_q6
        rows.extend([band(Q(23,160),Q(13,90),Q(639,40),-66,'q6 collision low-polynomial alias'),band(Q(13,90),Q(3,20),Q(223,40),6,'q6 collision zero-first-form')])
    if include_largeT_q8:
        assert include_smallcore_q8
        rows.extend([band(Q(23,190),Q(49,400),Q(27,5),9,'q8 largeT weak p15 POSTCUTOFF'),band(Q(49,400),Q(1,8),Q(53,8),-1,'q8 largeT strong p14 POSTCUTOFF')])
    if include_Rlarge_upper_q8:
        assert include_smallcore_q8
        rows.append(band(Q(13,110),Q(43,360),-Q(15,2),117,'q8 Rlarge upper full p14/p15 POSTCUTOFF'))
    if include_Rlarge_partial_q8:
        assert include_Rlarge_upper_q8
        rows.append(band(Q(2,17),Q(13,110),Q(29,10),29,'q8 Rlarge partial full p14/p15 POSTCUTOFF'))
    if include_E16_unit_q8:
        rows.append(band(Q(37,320),Q(7,60),Q(417,40),-34,'q8 E16 unit firstsource full p16 POSTCUTOFF'))
    ordered=sorted(rows,key=lambda r:r['left'])
    assert all(x['right']<=y['left']for x,y in zip(ordered,ordered[1:]))
    assert all(r['left']<r['right']and r['surplus']>=0 for r in rows)
    if include_typea_q7_left:
        q7=sorted([r for r in rows if r['name'].startswith('q7 ')],key=lambda r:r['left'])
        assert len(q7)==(6 if include_middle_q7 else 3) and q7[0]['left']==(Q(1,8)if include_middle_q7 else Q(37,280)) and q7[-1]['right']==Q(1,7)
        assert all(x['right']==y['left']for x,y in zip(q7,q7[1:]))
    known=sum((r['contribution']for r in rows),Q(0))
    surplus=sum((r['surplus']for r in rows),Q(0))
    needed=-C_lower-analytic_lower-known_outer_q2-known
    gap_H=H(0,Q(37,160))+H(Q(1,4),cut)
    if include_q5:gap_H-=H(Q(23,120),Q(1,5))
    if include_nine:gap_H-=H(Q(23,100),Q(37,160))
    if include_q6:gap_H-=H(Q(23,140),Q(1,6))
    if include_mixed and not sharp_q3:gap_H-=H(Q(2,7),cut)
    if include_mixed_q4 and not sharp_q4:gap_H-=H(q4_cut,Q(23,100))
    if include_seven_eight and not sharp_q3:gap_H-=H(Q(10089,35320),Q(2,7))
    if sharp_q3:gap_H-=H(Q(43,160),cut)
    if sharp_q4:gap_H-=H(Q(9,40),Q(23,100))
    if include_q7_strip and not include_full_q7:gap_H-=H(Q(18579,138280),Q(43,320))
    if include_full_q7:gap_H-=H(Q(37,280),Q(43,320))
    if include_low_seven:gap_H-=H(Q(13,50),Q(43,160))
    if include_q3_alias:gap_H-=H(Q(1,4),Q(13,50))
    if include_lower_q5:gap_H-=H(Q(37,200),Q(23,120))
    if include_lower_q6:gap_H-=H(Q(37,240),Q(23,140))
    if include_integral_q4:gap_H-=H(Q(13,60),Q(9,40))
    if include_middle_q5:gap_H-=H(Q(2,11),Q(37,200))
    if include_typea_q7_right:gap_H-=H(Q(49,360),Q(1,7))
    if include_typea_q7_left:gap_H-=H(Q(43,320),Q(49,360))
    if include_middle_q6:gap_H-=H(Q(43,280),Q(37,240))
    if include_folded_q5:gap_H-=H(Q(43,240),Q(2,11))
    if include_compressed_q4:gap_H-=H(Q(49,240),Q(43,200))
    if include_crt_q5:gap_H-=H(Q(1,6),Q(7,40))
    if include_upper_q5:gap_H-=H(Q(7,40),Q(43,240))
    if include_compressed_q6:gap_H-=H(Q(49,320),Q(43,280))
    if include_crt_q4:gap_H-=H(Q(1,5),Q(49,240))
    if include_crt_q6:gap_H-=H(Q(3,20),Q(49,320))
    if include_middle_q7:gap_H-=H(Q(1,8),Q(37,280))
    if include_upperstrip_q4:gap_H-=H(Q(43,200),Q(13,60))
    if include_collision_lower_q6:gap_H-=H(Q(1,7),Q(23,160))
    if include_smallcore_q8:gap_H-=H(Q(43,360),Q(23,190))
    if include_collision_upper_q6:gap_H-=H(Q(23,160),Q(3,20))
    if include_largeT_q8:gap_H-=H(Q(23,190),Q(1,8))
    if include_Rlarge_upper_q8:gap_H-=H(Q(13,110),Q(43,360))
    if include_Rlarge_partial_q8:gap_H-=H(Q(2,17),Q(13,110))
    if include_E16_unit_q8:gap_H-=H(Q(37,320),Q(7,60))
    allowance=gap_H-needed
    assert allowance==C_lower+analytic_lower+known_outer_q2+H(0,Q(1,3))+surplus
    margins={str(c):allowance-7*eta/Q(c)for c in [14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,32,40,48,50,60,100]}
    smallest=next(c for c in range(14,100)if allowance-7*eta/Q(c)>0)
    return dict(q3_cut=Q(1,4)if include_q3_alias else Q(13,50)if include_low_seven else Q(43,160)if sharp_q3 else Q(10089,35320)if include_seven_eight else Q(2,7)if include_mixed else cut,q4_cut=Q(13,60)if include_integral_q4 else Q(9,40)if sharp_q4 else q4_cut if include_mixed_q4 else Q(23,100)if include_nine else Q(37,160),includes_q5=include_q5,includes_nine_node_q4=include_nine,includes_q6=include_q6,includes_mixed_q3=include_mixed,includes_mixed_q4=include_mixed_q4,q4_mixed_index_factor=1 if sharp_q4 else mixed_q4_index if include_mixed_q4 else None,includes_seven_eight_q3=include_seven_eight,includes_sharp_twoform_q3=sharp_q3,includes_sharp_twoform_q4=sharp_q4,includes_q7_H0_substrip=include_q7_strip,includes_low_seven_q3=include_low_seven,includes_retained_alias_q3=include_q3_alias,includes_lower_q5=include_lower_q5,rows=rows,new_band_contribution=known,
        includes_lower_q6=include_lower_q6,
        includes_full_q7_A0=include_full_q7,
        includes_integral_lower_q4=include_integral_q4,
        includes_middle_q5=include_middle_q5,
        includes_typea_q7_right=include_typea_q7_right,
        includes_typea_q7_left=include_typea_q7_left,
        includes_middle_q6=include_middle_q6,
        includes_folded_q5=include_folded_q5,
        includes_compressed_q4=include_compressed_q4,includes_crt_q5=include_crt_q5,
        includes_upper_q5=include_upper_q5,includes_compressed_q6=include_compressed_q6,
        includes_crt_q4=include_crt_q4,includes_crt_q6=include_crt_q6,includes_middle_q7=include_middle_q7,includes_upperstrip_q4=include_upperstrip_q4,includes_collision_lower_q6=include_collision_lower_q6,includes_smallcore_q8=include_smallcore_q8,includes_collision_upper_q6=include_collision_upper_q6,includes_largeT_q8=include_largeT_q8,**({'includes_Rlarge_upper_q8':True}if include_Rlarge_upper_q8 else{}),**({'includes_Rlarge_partial_q8':True}if include_Rlarge_partial_q8 else{}),**({'includes_E16_unit_q8':True}if include_E16_unit_q8 else{}),
        q5_continuous_cut=Q(1,6)if include_upper_q5 else Q(43,240)if include_folded_q5 else None,
        q6_continuous_cut=Q(49,320)if include_compressed_q6 else Q(43,280)if include_middle_q6 else None,
        q4_latest_cut=Q(13,60)if include_integral_q4 else Q(9,40)if sharp_q4 else None,
        **({'new_q3_q4_q5_contribution':known}if include_q5 and not include_q6 else{'new_q3_q4_contribution':known}if not include_q5 and not include_q6 else{}),
        total_controlled_polarity=known_outer_q2+known,
        required_additional_aggregate_for_positive_growth=needed,
        H0_share_unresolved=gap_H,allowed_aggregate_loss_from_unresolved_H0=allowance,
        surplus_above_H0_from_new_bands=surplus,
        retained_H0_margin_by_integer_cutoff=margins,
        smallest_integer_smallprime_cutoff_supported_by_this_budget=smallest,
        pointwise_scope=('H0 still required on unresolved portions of K/C<p<=K/3; q5 band is removed from the open target.'if include_q5 else'H0 still required on K/C<p<=37K/160 and K/4<p<=q3_cut*K; all missing inequalities remain unproved.'))
def clean(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:clean(v)for k,v in x.items()}
    if isinstance(x,list):return list(map(clean,x))
    return x
gaps=[dict(name=n,band=[l,u],H0_share=H(l,u))for n,l,u in [
    ('deeper primes below q8 E16 unit branch',Q(1,48),Q(37,320)),
    ('q8 E16 partial firstsource',Q(7,60),Q(2,17)),
]]
out=clean(dict(label='COMPUTED',author='Codex gpt-6.1-sol lane A driver',
    cutoff_warning='latest_draft_frontier includes POST06SUPPORT; cutoff_0600_draft_frontier and immutable A-claim6-cutoff-0600/SNAPSHOT.json retain the actual report-cutoff state.',
    assumption='All contributing band theorems are PROOF-DRAFT/report CONJECTURE, with fixed local exceptions; inherited content/PNT/Jensen inputs remain draft. No missing H0/PD/E26 claim.',
    C_infinity_lower=C_lower,actual_analytic_lower=analytic_lower,old_outer_q2=known_outer_q2,
    established_draft_frontier=scenario(Q(13,45)),
    q3_alias_extension_draft_frontier=scenario(Q(23,80)),unresolved_H0_profile_bands=gaps,
    q5_unit_secondary_draft_frontier=scenario(Q(23,80),True),
    sixth_leaf_and_nine_node_draft_frontier=scenario(Q(23,80),True,True,True),
    mixed_q3_tertiary_draft_frontier=scenario(Q(23,80),True,True,True,True),
    mixed_q3_q4_bounded_index_draft_frontier=scenario(Q(23,80),True,True,True,True,True),
    coarse_folded_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True),
    sharp_twoform_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True),
    q7_strip_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True),
    lowseven_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True),
    full_q3_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True),
    full_q3_lower_q5_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True),
    lower_q6_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True),
    full_q7_A0_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True),
    shared_pencil_q7_right_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True),
    full_q7_Rsmall_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True),
    middle_q6_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True),
    folded_q5_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True),
    compressed_q4_q5_q6_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True,include_compressed_q4=True,include_crt_q5=True,include_upper_q5=True,include_compressed_q6=True),
    crt_widerq7_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True,include_compressed_q4=True,include_crt_q5=True,include_upper_q5=True,include_compressed_q6=True,include_crt_q4=True,include_crt_q6=True,include_middle_q7=True),
    full_q4_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True,include_compressed_q4=True,include_crt_q5=True,include_upper_q5=True,include_compressed_q6=True,include_crt_q4=True,include_crt_q6=True,include_middle_q7=True,include_upperstrip_q4=True),
    collision_lower_q6_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True,include_compressed_q4=True,include_crt_q5=True,include_upper_q5=True,include_compressed_q6=True,include_crt_q4=True,include_crt_q6=True,include_middle_q7=True,include_upperstrip_q4=True,include_collision_lower_q6=True),
    smallcore_q8_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True,include_compressed_q4=True,include_crt_q5=True,include_upper_q5=True,include_compressed_q6=True,include_crt_q4=True,include_crt_q6=True,include_middle_q7=True,include_upperstrip_q4=True,include_collision_lower_q6=True,include_smallcore_q8=True),
    cutoff_0600_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True,include_compressed_q4=True,include_crt_q5=True,include_upper_q5=True,include_compressed_q6=True,include_crt_q4=True,include_crt_q6=True,include_middle_q7=True,include_upperstrip_q4=True,include_collision_lower_q6=True,include_smallcore_q8=True,include_collision_upper_q6=True),
    post06_largeT_q8_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True,include_compressed_q4=True,include_crt_q5=True,include_upper_q5=True,include_compressed_q6=True,include_crt_q4=True,include_crt_q6=True,include_middle_q7=True,include_upperstrip_q4=True,include_collision_lower_q6=True,include_smallcore_q8=True,include_collision_upper_q6=True,include_largeT_q8=True),
    post06_Rlarge_upper_q8_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True,include_compressed_q4=True,include_crt_q5=True,include_upper_q5=True,include_compressed_q6=True,include_crt_q4=True,include_crt_q6=True,include_middle_q7=True,include_upperstrip_q4=True,include_collision_lower_q6=True,include_smallcore_q8=True,include_collision_upper_q6=True,include_largeT_q8=True,include_Rlarge_upper_q8=True),
    post06_Rlarge_partial_q8_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True,include_compressed_q4=True,include_crt_q5=True,include_upper_q5=True,include_compressed_q6=True,include_crt_q4=True,include_crt_q6=True,include_middle_q7=True,include_upperstrip_q4=True,include_collision_lower_q6=True,include_smallcore_q8=True,include_collision_upper_q6=True,include_largeT_q8=True,include_Rlarge_upper_q8=True,include_Rlarge_partial_q8=True),
    latest_draft_frontier=scenario(Q(23,80),True,True,True,True,True,mixed_q4_index=28,include_seven_eight=True,sharp_q3=True,sharp_q4=True,include_q7_strip=True,include_low_seven=True,include_q3_alias=True,include_lower_q5=True,include_lower_q6=True,include_full_q7=True,include_integral_q4=True,include_middle_q5=True,include_typea_q7_right=True,include_typea_q7_left=True,include_middle_q6=True,include_folded_q5=True,include_compressed_q4=True,include_crt_q5=True,include_upper_q5=True,include_compressed_q6=True,include_crt_q4=True,include_crt_q6=True,include_middle_q7=True,include_upperstrip_q4=True,include_collision_lower_q6=True,include_smallcore_q8=True,include_collision_upper_q6=True,include_largeT_q8=True,include_Rlarge_upper_q8=True,include_Rlarge_partial_q8=True,include_E16_unit_q8=True),
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()))
(HERE/'aggregate.json').write_text(json.dumps(out,indent=2)+'\n')
for key in ['established_draft_frontier','q3_alias_extension_draft_frontier','q5_unit_secondary_draft_frontier','sixth_leaf_and_nine_node_draft_frontier','mixed_q3_tertiary_draft_frontier','mixed_q3_q4_bounded_index_draft_frontier','latest_draft_frontier']:
    r=out[key]
    print(json.dumps({k:r[k]for k in ['q3_cut','includes_q5','new_band_contribution','required_additional_aggregate_for_positive_growth','allowed_aggregate_loss_from_unresolved_H0','smallest_integer_smallprime_cutoff_supported_by_this_budget','retained_H0_margin_by_integer_cutoff']}))
