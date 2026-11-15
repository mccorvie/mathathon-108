import Witness.Bounds
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace U11
noncomputable section
theorem logCell0 : (-5603:ℝ)/3200 ≤ Real.log ((25:ℝ)/144) ∧ Real.log ((25:ℝ)/144) ≤ (-8754687:ℝ)/5000000 := by
  have h := logPoly_bounds ((25:ℝ)/18) 24 (by norm_num)
  have he := log_scale ((25:ℝ)/144) ((25:ℝ)/18) (-3:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell1 : (-667657:ℝ)/2500000 ≤ Real.log ((49:ℝ)/64) ∧ Real.log ((49:ℝ)/64) ≤ (-2670627:ℝ)/10000000 := by
  have h := logPoly_bounds ((49:ℝ)/64) 24 (by norm_num)
  have he := log_scale ((49:ℝ)/64) ((49:ℝ)/64) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell2 : (-1618917:ℝ)/625000 ≤ Real.log ((3:ℝ)/40) ∧ Real.log ((3:ℝ)/40) ≤ (-25902671:ℝ)/10000000 := by
  have h := logPoly_bounds ((6:ℝ)/5) 24 (by norm_num)
  have he := log_scale ((3:ℝ)/40) ((6:ℝ)/5) (-4:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell3 : (384491:ℝ)/625000 ≤ Real.log ((37:ℝ)/20) ∧ Real.log ((37:ℝ)/20) ≤ (6151857:ℝ)/10000000 := by
  have h := logPoly_bounds ((37:ℝ)/40) 24 (by norm_num)
  have he := log_scale ((37:ℝ)/20) ((37:ℝ)/40) (1:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell4 : (70253:ℝ)/500000 ≤ Real.log ((150845:ℝ)/131072) ∧ Real.log ((150845:ℝ)/131072) ≤ (1405061:ℝ)/10000000 := by
  have h := logPoly_bounds ((150845:ℝ)/131072) 24 (by norm_num)
  have he := log_scale ((150845:ℝ)/131072) ((150845:ℝ)/131072) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell5 : (-785591:ℝ)/1000000 ≤ Real.log ((149373:ℝ)/327680) ∧ Real.log ((149373:ℝ)/327680) ≤ (-7855909:ℝ)/10000000 := by
  have h := logPoly_bounds ((149373:ℝ)/163840) 24 (by norm_num)
  have he := log_scale ((149373:ℝ)/327680) ((149373:ℝ)/163840) (-1:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell6 : (1122627:ℝ)/10000000 ≤ Real.log ((586577:ℝ)/524288) ∧ Real.log ((586577:ℝ)/524288) ≤ (280657:ℝ)/2500000 := by
  have h := logPoly_bounds ((586577:ℝ)/524288) 24 (by norm_num)
  have he := log_scale ((586577:ℝ)/524288) ((586577:ℝ)/524288) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell7 : (-4531621:ℝ)/5000000 ≤ Real.log ((1059079:ℝ)/2621440) ∧ Real.log ((1059079:ℝ)/2621440) ≤ (-9063241:ℝ)/10000000 := by
  have h := logPoly_bounds ((1059079:ℝ)/1310720) 24 (by norm_num)
  have he := log_scale ((1059079:ℝ)/2621440) ((1059079:ℝ)/1310720) (-1:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell8 : (89019:ℝ)/1000000 ≤ Real.log ((143275:ℝ)/131072) ∧ Real.log ((143275:ℝ)/131072) ≤ (890191:ℝ)/10000000 := by
  have h := logPoly_bounds ((143275:ℝ)/131072) 24 (by norm_num)
  have he := log_scale ((143275:ℝ)/131072) ((143275:ℝ)/131072) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell9 : (-5126273:ℝ)/5000000 ≤ Real.log ((235081:ℝ)/655360) ∧ Real.log ((235081:ℝ)/655360) ≤ (-2050509:ℝ)/2000000 := by
  have h := logPoly_bounds ((235081:ℝ)/163840) 24 (by norm_num)
  have he := log_scale ((235081:ℝ)/655360) ((235081:ℝ)/163840) (-2:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell10 : (87653:ℝ)/1250000 ≤ Real.log ((140593:ℝ)/131072) ∧ Real.log ((140593:ℝ)/131072) ≤ (28049:ℝ)/400000 := by
  have h := logPoly_bounds ((140593:ℝ)/131072) 24 (by norm_num)
  have he := log_scale ((140593:ℝ)/131072) ((140593:ℝ)/131072) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell11 : (-11421223:ℝ)/10000000 ≤ Real.log ((836609:ℝ)/2621440) ∧ Real.log ((836609:ℝ)/2621440) ≤ (-5710611:ℝ)/5000000 := by
  have h := logPoly_bounds ((836609:ℝ)/655360) 24 (by norm_num)
  have he := log_scale ((836609:ℝ)/2621440) ((836609:ℝ)/655360) (-2:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell12 : (549303:ℝ)/10000000 ≤ Real.log ((553893:ℝ)/524288) ∧ Real.log ((553893:ℝ)/524288) ≤ (68663:ℝ)/1250000 := by
  have h := logPoly_bounds ((553893:ℝ)/524288) 24 (by norm_num)
  have he := log_scale ((553893:ℝ)/524288) ((553893:ℝ)/524288) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell13 : (-1256661:ℝ)/1000000 ≤ Real.log ((746069:ℝ)/2621440) ∧ Real.log ((746069:ℝ)/2621440) ≤ (-12566609:ℝ)/10000000 := by
  have h := logPoly_bounds ((746069:ℝ)/655360) 24 (by norm_num)
  have he := log_scale ((746069:ℝ)/2621440) ((746069:ℝ)/655360) (-2:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell14 : (10707:ℝ)/250000 ≤ Real.log ((273615:ℝ)/262144) ∧ Real.log ((273615:ℝ)/262144) ≤ (428281:ℝ)/10000000 := by
  have h := logPoly_bounds ((273615:ℝ)/262144) 24 (by norm_num)
  have he := log_scale ((273615:ℝ)/262144) ((273615:ℝ)/262144) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell15 : (-13685481:ℝ)/10000000 ≤ Real.log ((333547:ℝ)/1310720) ∧ Real.log ((333547:ℝ)/1310720) ≤ (-342137:ℝ)/250000 := by
  have h := logPoly_bounds ((333547:ℝ)/327680) 24 (by norm_num)
  have he := log_scale ((333547:ℝ)/1310720) ((333547:ℝ)/327680) (-2:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell16 : (166327:ℝ)/5000000 ≤ Real.log ((271011:ℝ)/262144) ∧ Real.log ((271011:ℝ)/262144) ≤ (66531:ℝ)/2000000 := by
  have h := logPoly_bounds ((271011:ℝ)/262144) 24 (by norm_num)
  have he := log_scale ((271011:ℝ)/262144) ((271011:ℝ)/262144) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell17 : (-1477447:ℝ)/1000000 ≤ Real.log ((74783:ℝ)/327680) ∧ Real.log ((74783:ℝ)/327680) ≤ (-14774469:ℝ)/10000000 := by
  have h := logPoly_bounds ((74783:ℝ)/81920) 24 (by norm_num)
  have he := log_scale ((74783:ℝ)/327680) ((74783:ℝ)/81920) (-2:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell18 : (257579:ℝ)/10000000 ≤ Real.log ((33623:ℝ)/32768) ∧ Real.log ((33623:ℝ)/32768) ≤ (12879:ℝ)/500000 := by
  have h := logPoly_bounds ((33623:ℝ)/32768) 24 (by norm_num)
  have he := log_scale ((33623:ℝ)/32768) ((33623:ℝ)/32768) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell19 : (-15829721:ℝ)/10000000 ≤ Real.log ((538349:ℝ)/2621440) ∧ Real.log ((538349:ℝ)/2621440) ≤ (-395743:ℝ)/250000 := by
  have h := logPoly_bounds ((538349:ℝ)/655360) 24 (by norm_num)
  have he := log_scale ((538349:ℝ)/2621440) ((538349:ℝ)/655360) (-2:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell20 : (39793:ℝ)/2000000 ≤ Real.log ((66853:ℝ)/65536) ∧ Real.log ((66853:ℝ)/65536) ≤ (99483:ℝ)/5000000 := by
  have h := logPoly_bounds ((66853:ℝ)/65536) 24 (by norm_num)
  have he := log_scale ((66853:ℝ)/65536) ((66853:ℝ)/65536) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell21 : (-16847069:ℝ)/10000000 ≤ Real.log ((243137:ℝ)/1310720) ∧ Real.log ((243137:ℝ)/1310720) ≤ (-16847067:ℝ)/10000000 := by
  have h := logPoly_bounds ((243137:ℝ)/163840) 24 (by norm_num)
  have he := log_scale ((243137:ℝ)/1310720) ((243137:ℝ)/163840) (-3:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell22 : (15337:ℝ)/1000000 ≤ Real.log ((532391:ℝ)/524288) ∧ Real.log ((532391:ℝ)/524288) ≤ (153371:ℝ)/10000000 := by
  have h := logPoly_bounds ((532391:ℝ)/524288) 24 (by norm_num)
  have he := log_scale ((532391:ℝ)/524288) ((532391:ℝ)/524288) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell23 : (-8911049:ℝ)/5000000 ≤ Real.log ((441099:ℝ)/2621440) ∧ Real.log ((441099:ℝ)/2621440) ≤ (-17822097:ℝ)/10000000 := by
  have h := logPoly_bounds ((441099:ℝ)/327680) 24 (by norm_num)
  have he := log_scale ((441099:ℝ)/2621440) ((441099:ℝ)/327680) (-3:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell24 : (118051:ℝ)/10000000 ≤ Real.log ((265257:ℝ)/262144) ∧ Real.log ((265257:ℝ)/262144) ≤ (29513:ℝ)/2500000 := by
  have h := logPoly_bounds ((265257:ℝ)/262144) 24 (by norm_num)
  have he := log_scale ((265257:ℝ)/262144) ((265257:ℝ)/262144) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell25 : (-3750059:ℝ)/2000000 ≤ Real.log ((401999:ℝ)/2621440) ∧ Real.log ((401999:ℝ)/2621440) ≤ (-9375147:ℝ)/5000000 := by
  have h := logPoly_bounds ((401999:ℝ)/327680) 24 (by norm_num)
  have he := log_scale ((401999:ℝ)/2621440) ((401999:ℝ)/327680) (-3:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell26 : (45379:ℝ)/5000000 ≤ Real.log ((132267:ℝ)/131072) ∧ Real.log ((132267:ℝ)/131072) ≤ (90759:ℝ)/10000000 := by
  have h := logPoly_bounds ((132267:ℝ)/131072) 24 (by norm_num)
  have he := log_scale ((132267:ℝ)/131072) ((132267:ℝ)/131072) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell27 : (-1962679:ℝ)/1000000 ≤ Real.log ((46033:ℝ)/327680) ∧ Real.log ((46033:ℝ)/327680) ≤ (-19626789:ℝ)/10000000 := by
  have h := logPoly_bounds ((46033:ℝ)/40960) 24 (by norm_num)
  have he := log_scale ((46033:ℝ)/327680) ((46033:ℝ)/40960) (-3:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell28 : (69717:ℝ)/10000000 ≤ Real.log ((131989:ℝ)/131072) ∧ Real.log ((131989:ℝ)/131072) ≤ (34859:ℝ)/5000000 := by
  have h := logPoly_bounds ((131989:ℝ)/131072) 24 (by norm_num)
  have he := log_scale ((131989:ℝ)/131072) ((131989:ℝ)/131072) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell29 : (-10223429:ℝ)/5000000 ≤ Real.log ((339269:ℝ)/2621440) ∧ Real.log ((339269:ℝ)/2621440) ≤ (-20446857:ℝ)/10000000 := by
  have h := logPoly_bounds ((339269:ℝ)/327680) 24 (by norm_num)
  have he := log_scale ((339269:ℝ)/2621440) ((339269:ℝ)/327680) (-3:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell30 : (5351:ℝ)/1000000 ≤ Real.log ((527101:ℝ)/524288) ∧ Real.log ((527101:ℝ)/524288) ≤ (53511:ℝ)/10000000 := by
  have h := logPoly_bounds ((527101:ℝ)/524288) 24 (by norm_num)
  have he := log_scale ((527101:ℝ)/524288) ((527101:ℝ)/524288) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell31 : (-5301643:ℝ)/2500000 ≤ Real.log ((314449:ℝ)/2621440) ∧ Real.log ((314449:ℝ)/2621440) ≤ (-21206571:ℝ)/10000000 := by
  have h := logPoly_bounds ((314449:ℝ)/327680) 24 (by norm_num)
  have he := log_scale ((314449:ℝ)/2621440) ((314449:ℝ)/327680) (-3:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell32 : (20519:ℝ)/5000000 ≤ Real.log ((131611:ℝ)/131072) ∧ Real.log ((131611:ℝ)/131072) ≤ (41039:ℝ)/10000000 := by
  have h := logPoly_bounds ((131611:ℝ)/131072) 24 (by norm_num)
  have he := log_scale ((131611:ℝ)/131072) ((131611:ℝ)/131072) (0:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem logCell33 : (-21901843:ℝ)/10000000 ≤ Real.log ((293329:ℝ)/2621440) ∧ Real.log ((293329:ℝ)/2621440) ≤ (-10950921:ℝ)/5000000 := by
  have h := logPoly_bounds ((293329:ℝ)/327680) 24 (by norm_num)
  have he := log_scale ((293329:ℝ)/2621440) ((293329:ℝ)/327680) (-3:ℤ) (by norm_num) (by norm_num)
  have h2 := log2_bounds
  norm_num [logPoly, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1,h.2,h2.1,h2.2]

theorem sqrtCell0 : (341235:ℝ)/262144 ≤ Real.sqrt ((61:ℝ)/36) ∧ Real.sqrt ((61:ℝ)/36) ≤ (85309:ℝ)/65536 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell1 : (27417:ℝ)/32768 ≤ Real.sqrt ((10081:ℝ)/14400) ∧ Real.sqrt ((10081:ℝ)/14400) ≤ (219337:ℝ)/262144 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell2 : (20277:ℝ)/16384 ≤ Real.sqrt ((3529:ℝ)/2304) ∧ Real.sqrt ((3529:ℝ)/2304) ≤ (324433:ℝ)/262144 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell3 : (192155:ℝ)/262144 ≤ Real.sqrt ((30949:ℝ)/57600) ∧ Real.sqrt ((30949:ℝ)/57600) ≤ (48039:ℝ)/65536 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell4 : (310955:ℝ)/262144 ≤ Real.sqrt ((207481:ℝ)/147456) ∧ Real.sqrt ((207481:ℝ)/147456) ≤ (77739:ℝ)/65536 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell5 : (42101:ℝ)/65536 ≤ Real.sqrt ((1521361:ℝ)/3686400) ∧ Real.sqrt ((1521361:ℝ)/3686400) ≤ (168405:ℝ)/262144 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell6 : (300227:ℝ)/262144 ≤ Real.sqrt ((12378409:ℝ)/9437184) ∧ Real.sqrt ((12378409:ℝ)/9437184) ≤ (75057:ℝ)/65536 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell7 : (147661:ℝ)/262144 ≤ Real.sqrt ((74857729:ℝ)/235929600) ∧ Real.sqrt ((74857729:ℝ)/235929600) ≤ (73831:ℝ)/131072 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell8 : (72937:ℝ)/65536 ≤ Real.sqrt ((748099801:ℝ)/603979776) ∧ Real.sqrt ((748099801:ℝ)/603979776) ≤ (291749:ℝ)/262144 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell9 : (129553:ℝ)/262144 ≤ Real.sqrt ((3687935281:ℝ)/15099494400) ∧ Real.sqrt ((3687935281:ℝ)/15099494400) ≤ (64777:ℝ)/131072 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell10 : (285085:ℝ)/262144 ≤ Real.sqrt ((45716586889:ℝ)/38654705664) ∧ Real.sqrt ((45716586889:ℝ)/38654705664) ≤ (142543:ℝ)/131072 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell11 : (56879:ℝ)/131072 ≤ Real.sqrt ((181982848609:ℝ)/966367641600) ∧ Real.sqrt ((181982848609:ℝ)/966367641600) ≤ (113759:ℝ)/262144 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell12 : (279877:ℝ)/262144 ≤ Real.sqrt ((2819933342521:ℝ)/2473901162496) ∧ Real.sqrt ((2819933342521:ℝ)/2473901162496) ≤ (139939:ℝ)/131072 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell13 : (12499:ℝ)/32768 ≤ Real.sqrt ((8998696851601:ℝ)/61847529062400) ∧ Real.sqrt ((8998696851601:ℝ)/61847529062400) ≤ (99993:ℝ)/262144 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell14 : (275823:ℝ)/262144 ≤ Real.sqrt ((175285251220969:ℝ)/158329674399744) ∧ Real.sqrt ((175285251220969:ℝ)/158329674399744) ≤ (17239:ℝ)/16384 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell15 : (88009:ℝ)/262144 ≤ Real.sqrt ((446154530993089:ℝ)/3958241859993600) ∧ Real.sqrt ((446154530993089:ℝ)/3958241859993600) ≤ (44005:ℝ)/131072 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell16 : (272679:ℝ)/262144 ≤ Real.sqrt ((10963922425823641:ℝ)/10133099161583616) ∧ Real.sqrt ((10963922425823641:ℝ)/10133099161583616) ≤ (34085:ℝ)/32768 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell17 : (38797:ℝ)/131072 ≤ Real.sqrt ((22195548675598321:ℝ)/253327479039590400) ∧ Real.sqrt ((22195548675598321:ℝ)/253327479039590400) ≤ (77595:ℝ)/262144 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell18 : (135123:ℝ)/131072 ≤ Real.sqrt ((689228686289112649:ℝ)/648518346341351424) ∧ Real.sqrt ((689228686289112649:ℝ)/648518346341351424) ≤ (270247:ℝ)/262144 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell19 : (68559:ℝ)/262144 ≤ Real.sqrt ((1108956391148283169:ℝ)/16212958658533785600) ∧ Real.sqrt ((1108956391148283169:ℝ)/16212958658533785600) ≤ (4285:ℝ)/16384 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell20 : (268369:ℝ)/262144 ≤ Real.sqrt ((43499980823286791161:ℝ)/41505174165846491136) ∧ Real.sqrt ((43499980823286791161:ℝ)/41505174165846491136) ≤ (134185:ℝ)/131072 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell21 : (60739:ℝ)/262144 ≤ Real.sqrt ((55706831553079663441:ℝ)/1037629354146162278400) ∧ Real.sqrt ((55706831553079663441:ℝ)/1037629354146162278400) ≤ (15185:ℝ)/65536 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell22 : (266923:ℝ)/262144 ≤ Real.sqrt ((2754076672828750133929:ℝ)/2656331146614175432704) ∧ Real.sqrt ((2754076672828750133929:ℝ)/2656331146614175432704) ≤ (66731:ℝ)/65536 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell23 : (6749:ℝ)/32768 ≤ Real.sqrt ((2817184722856985950849:ℝ)/66408278665354385817600) ∧ Real.sqrt ((2817184722856985950849:ℝ)/66408278665354385817600) ≤ (53993:ℝ)/262144 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell24 : (265811:ℝ)/262144 ≤ Real.sqrt ((174794724167821388053081:ℝ)/170005193383307227693056) ∧ Real.sqrt ((174794724167821388053081:ℝ)/170005193383307227693056) ≤ (66453:ℝ)/65536 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell25 : (48193:ℝ)/262144 ≤ Real.sqrt ((143645249932381587894961:ℝ)/4250129834582680692326400) ∧ Real.sqrt ((143645249932381587894961:ℝ)/4250129834582680692326400) ≤ (24097:ℝ)/131072 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell26 : (66239:ℝ)/65536 ≤ Real.sqrt ((11115019384972856429996809:ℝ)/10880332376531662572355584) ∧ Real.sqrt ((11115019384972856429996809:ℝ)/10880332376531662572355584) ≤ (264957:ℝ)/262144 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell27 : (43229:ℝ)/262144 ≤ Real.sqrt ((7397221951479611490268129:ℝ)/272008309413291564308889600) ∧ Real.sqrt ((7397221951479611490268129:ℝ)/272008309413291564308889600) ≤ (21615:ℝ)/131072 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell28 : (264299:ℝ)/262144 ≤ Real.sqrt ((707840935511644903655177401:ℝ)/696341272098026404630757376) ∧ Real.sqrt ((707840935511644903655177401:ℝ)/696341272098026404630757376) ≤ (66075:ℝ)/65536 := by
  apply sqrt_bounds <;> norm_num

theorem sqrtCell29 : (39005:ℝ)/262144 ≤ Real.sqrt ((385414576729247438761700881:ℝ)/17408531802450660115768934400) ∧ Real.sqrt ((385414576729247438761700881:ℝ)/17408531802450660115768934400) ≤ (19503:ℝ)/131072 := by
  apply sqrt_bounds <;> norm_num

end
end U11
