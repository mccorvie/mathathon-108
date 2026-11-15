import Witness.Cells
import Witness.Expression
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace U11
noncomputable section
theorem fieldCell0 : W (width (0:Fin 15)) ≤ (35072805959:ℝ)/10240000000 := by
  have h1 : (341235:ℝ)/262144≤Real.sqrt (1+width (0:Fin 15)) ∧ Real.sqrt (1+width (0:Fin 15))≤(85309:ℝ)/65536 := by
    convert sqrtCell0 using 1 <;> norm_num [width]
  have ha : (27417:ℝ)/32768≤Real.sqrt (alpha^2+width (0:Fin 15)) ∧ Real.sqrt (alpha^2+width (0:Fin 15))≤(219337:ℝ)/262144 := by
    convert sqrtCell1 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (0:Fin 15)))/2)≤(1405061:ℝ)/10000000 := by
    calc Real.log ((1+Real.sqrt (1+width (0:Fin 15)))/2) ≤ Real.log ((150845:ℝ)/131072) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (1405061:ℝ)/10000000 := logCell4.2
  have hloga : (-785591:ℝ)/1000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (0:Fin 15)))/2) := by
    calc (-785591:ℝ)/1000000 ≤ Real.log ((149373:ℝ)/327680) := logCell5.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (0:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (0:Fin 15)) (rootWidth (0:Fin 15)) ((341235:ℝ)/262144) ((85309:ℝ)/65536) ((27417:ℝ)/32768) ((219337:ℝ)/262144) ((1405061:ℝ)/10000000) ((-785591:ℝ)/1000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell1 : W (width (1:Fin 15)) ≤ (19111688107:ℝ)/6400000000 := by
  have h1 : (20277:ℝ)/16384≤Real.sqrt (1+width (1:Fin 15)) ∧ Real.sqrt (1+width (1:Fin 15))≤(324433:ℝ)/262144 := by
    convert sqrtCell2 using 1 <;> norm_num [width]
  have ha : (192155:ℝ)/262144≤Real.sqrt (alpha^2+width (1:Fin 15)) ∧ Real.sqrt (alpha^2+width (1:Fin 15))≤(48039:ℝ)/65536 := by
    convert sqrtCell3 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (1:Fin 15)))/2)≤(280657:ℝ)/2500000 := by
    calc Real.log ((1+Real.sqrt (1+width (1:Fin 15)))/2) ≤ Real.log ((586577:ℝ)/524288) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (280657:ℝ)/2500000 := logCell6.2
  have hloga : (-4531621:ℝ)/5000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (1:Fin 15)))/2) := by
    calc (-4531621:ℝ)/5000000 ≤ Real.log ((1059079:ℝ)/2621440) := logCell7.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (1:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (1:Fin 15)) (rootWidth (1:Fin 15)) ((20277:ℝ)/16384) ((324433:ℝ)/262144) ((192155:ℝ)/262144) ((48039:ℝ)/65536) ((280657:ℝ)/2500000) ((-4531621:ℝ)/5000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell2 : W (width (2:Fin 15)) ≤ (133591709683:ℝ)/51200000000 := by
  have h1 : (310955:ℝ)/262144≤Real.sqrt (1+width (2:Fin 15)) ∧ Real.sqrt (1+width (2:Fin 15))≤(77739:ℝ)/65536 := by
    convert sqrtCell4 using 1 <;> norm_num [width]
  have ha : (42101:ℝ)/65536≤Real.sqrt (alpha^2+width (2:Fin 15)) ∧ Real.sqrt (alpha^2+width (2:Fin 15))≤(168405:ℝ)/262144 := by
    convert sqrtCell5 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (2:Fin 15)))/2)≤(890191:ℝ)/10000000 := by
    calc Real.log ((1+Real.sqrt (1+width (2:Fin 15)))/2) ≤ Real.log ((143275:ℝ)/131072) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (890191:ℝ)/10000000 := logCell8.2
  have hloga : (-5126273:ℝ)/5000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (2:Fin 15)))/2) := by
    calc (-5126273:ℝ)/5000000 ≤ Real.log ((235081:ℝ)/655360) := logCell9.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (2:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (2:Fin 15)) (rootWidth (2:Fin 15)) ((310955:ℝ)/262144) ((77739:ℝ)/65536) ((42101:ℝ)/65536) ((168405:ℝ)/262144) ((890191:ℝ)/10000000) ((-5126273:ℝ)/5000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell3 : W (width (3:Fin 15)) ≤ (117116180209:ℝ)/51200000000 := by
  have h1 : (300227:ℝ)/262144≤Real.sqrt (1+width (3:Fin 15)) ∧ Real.sqrt (1+width (3:Fin 15))≤(75057:ℝ)/65536 := by
    convert sqrtCell6 using 1 <;> norm_num [width]
  have ha : (147661:ℝ)/262144≤Real.sqrt (alpha^2+width (3:Fin 15)) ∧ Real.sqrt (alpha^2+width (3:Fin 15))≤(73831:ℝ)/131072 := by
    convert sqrtCell7 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (3:Fin 15)))/2)≤(28049:ℝ)/400000 := by
    calc Real.log ((1+Real.sqrt (1+width (3:Fin 15)))/2) ≤ Real.log ((140593:ℝ)/131072) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (28049:ℝ)/400000 := logCell10.2
  have hloga : (-11421223:ℝ)/10000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (3:Fin 15)))/2) := by
    calc (-11421223:ℝ)/10000000 ≤ Real.log ((836609:ℝ)/2621440) := logCell11.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (3:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (3:Fin 15)) (rootWidth (3:Fin 15)) ((300227:ℝ)/262144) ((75057:ℝ)/65536) ((147661:ℝ)/262144) ((73831:ℝ)/131072) ((28049:ℝ)/400000) ((-11421223:ℝ)/10000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell4 : W (width (4:Fin 15)) ≤ (2578685921:ℝ)/1280000000 := by
  have h1 : (72937:ℝ)/65536≤Real.sqrt (1+width (4:Fin 15)) ∧ Real.sqrt (1+width (4:Fin 15))≤(291749:ℝ)/262144 := by
    convert sqrtCell8 using 1 <;> norm_num [width]
  have ha : (129553:ℝ)/262144≤Real.sqrt (alpha^2+width (4:Fin 15)) ∧ Real.sqrt (alpha^2+width (4:Fin 15))≤(64777:ℝ)/131072 := by
    convert sqrtCell9 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (4:Fin 15)))/2)≤(68663:ℝ)/1250000 := by
    calc Real.log ((1+Real.sqrt (1+width (4:Fin 15)))/2) ≤ Real.log ((553893:ℝ)/524288) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (68663:ℝ)/1250000 := logCell12.2
  have hloga : (-1256661:ℝ)/1000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (4:Fin 15)))/2) := by
    calc (-1256661:ℝ)/1000000 ≤ Real.log ((746069:ℝ)/2621440) := logCell13.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (4:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (4:Fin 15)) (rootWidth (4:Fin 15)) ((72937:ℝ)/65536) ((291749:ℝ)/262144) ((129553:ℝ)/262144) ((64777:ℝ)/131072) ((68663:ℝ)/1250000) ((-1256661:ℝ)/1000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell5 : W (width (5:Fin 15)) ≤ (91404934513:ℝ)/51200000000 := by
  have h1 : (285085:ℝ)/262144≤Real.sqrt (1+width (5:Fin 15)) ∧ Real.sqrt (1+width (5:Fin 15))≤(142543:ℝ)/131072 := by
    convert sqrtCell10 using 1 <;> norm_num [width]
  have ha : (56879:ℝ)/131072≤Real.sqrt (alpha^2+width (5:Fin 15)) ∧ Real.sqrt (alpha^2+width (5:Fin 15))≤(113759:ℝ)/262144 := by
    convert sqrtCell11 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (5:Fin 15)))/2)≤(428281:ℝ)/10000000 := by
    calc Real.log ((1+Real.sqrt (1+width (5:Fin 15)))/2) ≤ Real.log ((273615:ℝ)/262144) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (428281:ℝ)/10000000 := logCell14.2
  have hloga : (-13685481:ℝ)/10000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (5:Fin 15)))/2) := by
    calc (-13685481:ℝ)/10000000 ≤ Real.log ((333547:ℝ)/1310720) := logCell15.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (5:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (5:Fin 15)) (rootWidth (5:Fin 15)) ((285085:ℝ)/262144) ((142543:ℝ)/131072) ((56879:ℝ)/131072) ((113759:ℝ)/262144) ((428281:ℝ)/10000000) ((-13685481:ℝ)/10000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell6 : W (width (6:Fin 15)) ≤ (32650873609:ℝ)/20480000000 := by
  have h1 : (279877:ℝ)/262144≤Real.sqrt (1+width (6:Fin 15)) ∧ Real.sqrt (1+width (6:Fin 15))≤(139939:ℝ)/131072 := by
    convert sqrtCell12 using 1 <;> norm_num [width]
  have ha : (12499:ℝ)/32768≤Real.sqrt (alpha^2+width (6:Fin 15)) ∧ Real.sqrt (alpha^2+width (6:Fin 15))≤(99993:ℝ)/262144 := by
    convert sqrtCell13 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (6:Fin 15)))/2)≤(66531:ℝ)/2000000 := by
    calc Real.log ((1+Real.sqrt (1+width (6:Fin 15)))/2) ≤ Real.log ((271011:ℝ)/262144) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (66531:ℝ)/2000000 := logCell16.2
  have hloga : (-1477447:ℝ)/1000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (6:Fin 15)))/2) := by
    calc (-1477447:ℝ)/1000000 ≤ Real.log ((74783:ℝ)/327680) := logCell17.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (6:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (6:Fin 15)) (rootWidth (6:Fin 15)) ((279877:ℝ)/262144) ((139939:ℝ)/131072) ((12499:ℝ)/32768) ((99993:ℝ)/262144) ((66531:ℝ)/2000000) ((-1477447:ℝ)/1000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell7 : W (width (7:Fin 15)) ≤ (1177294405213:ℝ)/819200000000 := by
  have h1 : (275823:ℝ)/262144≤Real.sqrt (1+width (7:Fin 15)) ∧ Real.sqrt (1+width (7:Fin 15))≤(17239:ℝ)/16384 := by
    convert sqrtCell14 using 1 <;> norm_num [width]
  have ha : (88009:ℝ)/262144≤Real.sqrt (alpha^2+width (7:Fin 15)) ∧ Real.sqrt (alpha^2+width (7:Fin 15))≤(44005:ℝ)/131072 := by
    convert sqrtCell15 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (7:Fin 15)))/2)≤(12879:ℝ)/500000 := by
    calc Real.log ((1+Real.sqrt (1+width (7:Fin 15)))/2) ≤ Real.log ((33623:ℝ)/32768) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (12879:ℝ)/500000 := logCell18.2
  have hloga : (-15829721:ℝ)/10000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (7:Fin 15)))/2) := by
    calc (-15829721:ℝ)/10000000 ≤ Real.log ((538349:ℝ)/2621440) := logCell19.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (7:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (7:Fin 15)) (rootWidth (7:Fin 15)) ((275823:ℝ)/262144) ((17239:ℝ)/16384) ((88009:ℝ)/262144) ((44005:ℝ)/131072) ((12879:ℝ)/500000) ((-15829721:ℝ)/10000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell8 : W (width (8:Fin 15)) ≤ (8582767388251:ℝ)/6553600000000 := by
  have h1 : (272679:ℝ)/262144≤Real.sqrt (1+width (8:Fin 15)) ∧ Real.sqrt (1+width (8:Fin 15))≤(34085:ℝ)/32768 := by
    convert sqrtCell16 using 1 <;> norm_num [width]
  have ha : (38797:ℝ)/131072≤Real.sqrt (alpha^2+width (8:Fin 15)) ∧ Real.sqrt (alpha^2+width (8:Fin 15))≤(77595:ℝ)/262144 := by
    convert sqrtCell17 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (8:Fin 15)))/2)≤(99483:ℝ)/5000000 := by
    calc Real.log ((1+Real.sqrt (1+width (8:Fin 15)))/2) ≤ Real.log ((66853:ℝ)/65536) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (99483:ℝ)/5000000 := logCell20.2
  have hloga : (-16847069:ℝ)/10000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (8:Fin 15)))/2) := by
    calc (-16847069:ℝ)/10000000 ≤ Real.log ((243137:ℝ)/1310720) := logCell21.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (8:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (8:Fin 15)) (rootWidth (8:Fin 15)) ((272679:ℝ)/262144) ((34085:ℝ)/32768) ((38797:ℝ)/131072) ((77595:ℝ)/262144) ((99483:ℝ)/5000000) ((-16847069:ℝ)/10000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell9 : W (width (9:Fin 15)) ≤ (63333381871101:ℝ)/52428800000000 := by
  have h1 : (135123:ℝ)/131072≤Real.sqrt (1+width (9:Fin 15)) ∧ Real.sqrt (1+width (9:Fin 15))≤(270247:ℝ)/262144 := by
    convert sqrtCell18 using 1 <;> norm_num [width]
  have ha : (68559:ℝ)/262144≤Real.sqrt (alpha^2+width (9:Fin 15)) ∧ Real.sqrt (alpha^2+width (9:Fin 15))≤(4285:ℝ)/16384 := by
    convert sqrtCell19 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (9:Fin 15)))/2)≤(153371:ℝ)/10000000 := by
    calc Real.log ((1+Real.sqrt (1+width (9:Fin 15)))/2) ≤ Real.log ((532391:ℝ)/524288) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (153371:ℝ)/10000000 := logCell22.2
  have hloga : (-8911049:ℝ)/5000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (9:Fin 15)))/2) := by
    calc (-8911049:ℝ)/5000000 ≤ Real.log ((441099:ℝ)/2621440) := logCell23.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (9:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (9:Fin 15)) (rootWidth (9:Fin 15)) ((135123:ℝ)/131072) ((270247:ℝ)/262144) ((68559:ℝ)/262144) ((4285:ℝ)/16384) ((153371:ℝ)/10000000) ((-8911049:ℝ)/5000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell10 : W (width (10:Fin 15)) ≤ (94684116938031:ℝ)/83886080000000 := by
  have h1 : (268369:ℝ)/262144≤Real.sqrt (1+width (10:Fin 15)) ∧ Real.sqrt (1+width (10:Fin 15))≤(134185:ℝ)/131072 := by
    convert sqrtCell20 using 1 <;> norm_num [width]
  have ha : (60739:ℝ)/262144≤Real.sqrt (alpha^2+width (10:Fin 15)) ∧ Real.sqrt (alpha^2+width (10:Fin 15))≤(15185:ℝ)/65536 := by
    convert sqrtCell21 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (10:Fin 15)))/2)≤(29513:ℝ)/2500000 := by
    calc Real.log ((1+Real.sqrt (1+width (10:Fin 15)))/2) ≤ Real.log ((265257:ℝ)/262144) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (29513:ℝ)/2500000 := logCell24.2
  have hloga : (-3750059:ℝ)/2000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (10:Fin 15)))/2) := by
    calc (-3750059:ℝ)/2000000 ≤ Real.log ((401999:ℝ)/2621440) := logCell25.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (10:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (10:Fin 15)) (rootWidth (10:Fin 15)) ((268369:ℝ)/262144) ((134185:ℝ)/131072) ((60739:ℝ)/262144) ((15185:ℝ)/65536) ((29513:ℝ)/2500000) ((-3750059:ℝ)/2000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell11 : W (width (11:Fin 15)) ≤ (717225830571081:ℝ)/671088640000000 := by
  have h1 : (266923:ℝ)/262144≤Real.sqrt (1+width (11:Fin 15)) ∧ Real.sqrt (1+width (11:Fin 15))≤(66731:ℝ)/65536 := by
    convert sqrtCell22 using 1 <;> norm_num [width]
  have ha : (6749:ℝ)/32768≤Real.sqrt (alpha^2+width (11:Fin 15)) ∧ Real.sqrt (alpha^2+width (11:Fin 15))≤(53993:ℝ)/262144 := by
    convert sqrtCell23 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (11:Fin 15)))/2)≤(90759:ℝ)/10000000 := by
    calc Real.log ((1+Real.sqrt (1+width (11:Fin 15)))/2) ≤ Real.log ((132267:ℝ)/131072) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (90759:ℝ)/10000000 := logCell26.2
  have hloga : (-1962679:ℝ)/1000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (11:Fin 15)))/2) := by
    calc (-1962679:ℝ)/1000000 ≤ Real.log ((46033:ℝ)/327680) := logCell27.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (11:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (11:Fin 15)) (rootWidth (11:Fin 15)) ((266923:ℝ)/262144) ((66731:ℝ)/65536) ((6749:ℝ)/32768) ((53993:ℝ)/262144) ((90759:ℝ)/10000000) ((-1962679:ℝ)/1000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell12 : W (width (12:Fin 15)) ≤ (27521180856950267:ℝ)/26843545600000000 := by
  have h1 : (265811:ℝ)/262144≤Real.sqrt (1+width (12:Fin 15)) ∧ Real.sqrt (1+width (12:Fin 15))≤(66453:ℝ)/65536 := by
    convert sqrtCell24 using 1 <;> norm_num [width]
  have ha : (48193:ℝ)/262144≤Real.sqrt (alpha^2+width (12:Fin 15)) ∧ Real.sqrt (alpha^2+width (12:Fin 15))≤(24097:ℝ)/131072 := by
    convert sqrtCell25 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (12:Fin 15)))/2)≤(34859:ℝ)/5000000 := by
    calc Real.log ((1+Real.sqrt (1+width (12:Fin 15)))/2) ≤ Real.log ((131989:ℝ)/131072) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (34859:ℝ)/5000000 := logCell28.2
  have hloga : (-10223429:ℝ)/5000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (12:Fin 15)))/2) := by
    calc (-10223429:ℝ)/5000000 ≤ Real.log ((339269:ℝ)/2621440) := logCell29.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (12:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (12:Fin 15)) (rootWidth (12:Fin 15)) ((265811:ℝ)/262144) ((66453:ℝ)/65536) ((48193:ℝ)/262144) ((24097:ℝ)/131072) ((34859:ℝ)/5000000) ((-10223429:ℝ)/5000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell13 : W (width (13:Fin 15)) ≤ (213793112499802589:ℝ)/214748364800000000 := by
  have h1 : (66239:ℝ)/65536≤Real.sqrt (1+width (13:Fin 15)) ∧ Real.sqrt (1+width (13:Fin 15))≤(264957:ℝ)/262144 := by
    convert sqrtCell26 using 1 <;> norm_num [width]
  have ha : (43229:ℝ)/262144≤Real.sqrt (alpha^2+width (13:Fin 15)) ∧ Real.sqrt (alpha^2+width (13:Fin 15))≤(21615:ℝ)/131072 := by
    convert sqrtCell27 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (13:Fin 15)))/2)≤(53511:ℝ)/10000000 := by
    calc Real.log ((1+Real.sqrt (1+width (13:Fin 15)))/2) ≤ Real.log ((527101:ℝ)/524288) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (53511:ℝ)/10000000 := logCell30.2
  have hloga : (-5301643:ℝ)/2500000≤Real.log ((alpha+Real.sqrt (alpha^2+width (13:Fin 15)))/2) := by
    calc (-5301643:ℝ)/2500000 ≤ Real.log ((314449:ℝ)/2621440) := logCell31.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (13:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (13:Fin 15)) (rootWidth (13:Fin 15)) ((66239:ℝ)/65536) ((264957:ℝ)/262144) ((43229:ℝ)/262144) ((21615:ℝ)/131072) ((53511:ℝ)/10000000) ((-5301643:ℝ)/2500000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

theorem fieldCell14 : W (width (14:Fin 15)) ≤ (1679220438927195403:ℝ)/1717986918400000000 := by
  have h1 : (264299:ℝ)/262144≤Real.sqrt (1+width (14:Fin 15)) ∧ Real.sqrt (1+width (14:Fin 15))≤(66075:ℝ)/65536 := by
    convert sqrtCell28 using 1 <;> norm_num [width]
  have ha : (39005:ℝ)/262144≤Real.sqrt (alpha^2+width (14:Fin 15)) ∧ Real.sqrt (alpha^2+width (14:Fin 15))≤(19503:ℝ)/131072 := by
    convert sqrtCell29 using 1 <;> norm_num [width,alpha]
  have hlog1 : Real.log ((1+Real.sqrt (1+width (14:Fin 15)))/2)≤(41039:ℝ)/10000000 := by
    calc Real.log ((1+Real.sqrt (1+width (14:Fin 15)))/2) ≤ Real.log ((131611:ℝ)/131072) := by
          apply Real.log_le_log (by positivity)
          linarith [h1.2]
         _ ≤ (41039:ℝ)/10000000 := logCell32.2
  have hloga : (-21901843:ℝ)/10000000≤Real.log ((alpha+Real.sqrt (alpha^2+width (14:Fin 15)))/2) := by
    calc (-21901843:ℝ)/10000000 ≤ Real.log ((293329:ℝ)/2621440) := logCell33.1
         _ ≤ Real.log ((alpha+Real.sqrt (alpha^2+width (14:Fin 15)))/2) := by
          apply Real.log_le_log (by norm_num)
          dsimp [alpha] at *
          linarith [ha.1]
  have hw := W_upper (width (14:Fin 15)) (rootWidth (14:Fin 15)) ((264299:ℝ)/262144) ((66075:ℝ)/65536) ((39005:ℝ)/262144) ((19503:ℝ)/131072) ((41039:ℝ)/10000000) ((-21901843:ℝ)/10000000) (sqrt_width _) h1 ha hlog1 hloga
  norm_num [rootWidth] at hw ⊢
  exact hw

def fieldCeil : Fin 15 → ℝ := ![(35072805959:ℝ)/10240000000,(19111688107:ℝ)/6400000000,(133591709683:ℝ)/51200000000,(117116180209:ℝ)/51200000000,(2578685921:ℝ)/1280000000,(91404934513:ℝ)/51200000000,(32650873609:ℝ)/20480000000,(1177294405213:ℝ)/819200000000,(8582767388251:ℝ)/6553600000000,(63333381871101:ℝ)/52428800000000,(94684116938031:ℝ)/83886080000000,(717225830571081:ℝ)/671088640000000,(27521180856950267:ℝ)/26843545600000000,(213793112499802589:ℝ)/214748364800000000,(1679220438927195403:ℝ)/1717986918400000000]
theorem field_ceil (j : Fin 15) : W (width j) ≤ fieldCeil j := by
  fin_cases j
  · exact fieldCell0
  · exact fieldCell1
  · exact fieldCell2
  · exact fieldCell3
  · exact fieldCell4
  · exact fieldCell5
  · exact fieldCell6
  · exact fieldCell7
  · exact fieldCell8
  · exact fieldCell9
  · exact fieldCell10
  · exact fieldCell11
  · exact fieldCell12
  · exact fieldCell13
  · exact fieldCell14
theorem mass_nonneg (j : Fin 15) : 0≤mass j := by
  fin_cases j <;> norm_num [mass]

theorem field_sum_le : (∑ j : Fin 15, mass j*W (width j)) ≤ ∑ j : Fin 15, mass j*fieldCeil j := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (field_ceil j) (mass_nonneg j)

end
end U11
