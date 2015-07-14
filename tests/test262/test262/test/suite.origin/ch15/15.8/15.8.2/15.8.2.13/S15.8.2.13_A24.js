// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    Math.pow, recommended that implementations use the approximation
    algorithms for IEEE 754 arithmetic contained in fdlibm
es5id: 15.8.2.13_A24
description: >
    Checking if Math.pow(argument1, argument2) is approximately equals
    to its mathematical value on the set of 64 argument1 values and 64
    argument2 values; all the sample values is calculated with LibC
includes:
    - math_precision.js
    - math_isequal.js
---*/

// CHECK#1
vnum = 64;
var x1 = new Array();
x1[0] = 0.00000000000000000000;
x1[1] = 0.25396825396825395000;
x1[2] = 0.50793650793650791000;
x1[3] = 0.76190476190476186000;
x1[4] = 1.01587301587301580000;
x1[5] = 1.26984126984126980000;
x1[6] = 1.52380952380952370000;
x1[7] = 1.77777777777777770000;
x1[8] = 2.03174603174603160000;
x1[9] = 2.28571428571428560000;
x1[10] = 2.53968253968253950000;
x1[11] = 2.79365079365079350000;
x1[12] = 3.04761904761904740000;
x1[13] = 3.30158730158730140000;
x1[14] = 3.55555555555555540000;
x1[15] = 3.80952380952380930000;
x1[16] = 4.06349206349206330000;
x1[17] = 4.31746031746031720000;
x1[18] = 4.57142857142857120000;
x1[19] = 4.82539682539682510000;
x1[20] = 5.07936507936507910000;
x1[21] = 5.33333333333333300000;
x1[22] = 5.58730158730158700000;
x1[23] = 5.84126984126984090000;
x1[24] = 6.09523809523809490000;
x1[25] = 6.34920634920634890000;
x1[26] = 6.60317460317460280000;
x1[27] = 6.85714285714285680000;
x1[28] = 7.11111111111111070000;
x1[29] = 7.36507936507936470000;
x1[30] = 7.61904761904761860000;
x1[31] = 7.87301587301587260000;
x1[32] = 8.12698412698412650000;
x1[33] = 8.38095238095238140000;
x1[34] = 8.63492063492063440000;
x1[35] = 8.88888888888888930000;
x1[36] = 9.14285714285714230000;
x1[37] = 9.39682539682539720000;
x1[38] = 9.65079365079365030000;
x1[39] = 9.90476190476190510000;
x1[40] = 10.15873015873015800000;
x1[41] = 10.41269841269841300000;
x1[42] = 10.66666666666666600000;
x1[43] = 10.92063492063492100000;
x1[44] = 11.17460317460317400000;
x1[45] = 11.42857142857142900000;
x1[46] = 11.68253968253968200000;
x1[47] = 11.93650793650793700000;
x1[48] = 12.19047619047619000000;
x1[49] = 12.44444444444444500000;
x1[50] = 12.69841269841269800000;
x1[51] = 12.95238095238095300000;
x1[52] = 13.20634920634920600000;
x1[53] = 13.46031746031746000000;
x1[54] = 13.71428571428571400000;
x1[55] = 13.96825396825396800000;
x1[56] = 14.22222222222222100000;
x1[57] = 14.47619047619047600000;
x1[58] = 14.73015873015872900000;
x1[59] = 14.98412698412698400000;
x1[60] = 15.23809523809523700000;
x1[61] = 15.49206349206349200000;
x1[62] = 15.74603174603174500000;
x1[63] = 16.00000000000000000000;



var x2 = new Array();
x2[0] = -16.00000000000000000000;
x2[1] = -15.49206349206349200000;
x2[2] = -14.98412698412698400000;
x2[3] = -14.47619047619047600000;
x2[4] = -13.96825396825396800000;
x2[5] = -13.46031746031746000000;
x2[6] = -12.95238095238095300000;
x2[7] = -12.44444444444444500000;
x2[8] = -11.93650793650793700000;
x2[9] = -11.42857142857142900000;
x2[10] = -10.92063492063492100000;
x2[11] = -10.41269841269841300000;
x2[12] = -9.90476190476190510000;
x2[13] = -9.39682539682539720000;
x2[14] = -8.88888888888888930000;
x2[15] = -8.38095238095238140000;
x2[16] = -7.87301587301587350000;
x2[17] = -7.36507936507936560000;
x2[18] = -6.85714285714285770000;
x2[19] = -6.34920634920634970000;
x2[20] = -5.84126984126984180000;
x2[21] = -5.33333333333333390000;
x2[22] = -4.82539682539682600000;
x2[23] = -4.31746031746031810000;
x2[24] = -3.80952380952381020000;
x2[25] = -3.30158730158730230000;
x2[26] = -2.79365079365079440000;
x2[27] = -2.28571428571428650000;
x2[28] = -1.77777777777777860000;
x2[29] = -1.26984126984127070000;
x2[30] = -0.76190476190476275000;
x2[31] = -0.25396825396825484000;
x2[32] = 0.25396825396825307000;
x2[33] = 0.76190476190476275000;
x2[34] = 1.26984126984126890000;
x2[35] = 1.77777777777777860000;
x2[36] = 2.28571428571428470000;
x2[37] = 2.79365079365079440000;
x2[38] = 3.30158730158730050000;
x2[39] = 3.80952380952381020000;
x2[40] = 4.31746031746031630000;
x2[41] = 4.82539682539682600000;
x2[42] = 5.33333333333333210000;
x2[43] = 5.84126984126984180000;
x2[44] = 6.34920634920634800000;
x2[45] = 6.85714285714285770000;
x2[46] = 7.36507936507936380000;
x2[47] = 7.87301587301587350000;
x2[48] = 8.38095238095237960000;
x2[49] = 8.88888888888888930000;
x2[50] = 9.39682539682539540000;
x2[51] = 9.90476190476190510000;
x2[52] = 10.41269841269841100000;
x2[53] = 10.92063492063492100000;
x2[54] = 11.42857142857142700000;
x2[55] = 11.93650793650793700000;
x2[56] = 12.44444444444444300000;
x2[57] = 12.95238095238095300000;
x2[58] = 13.46031746031745900000;
x2[59] = 13.96825396825396800000;
x2[60] = 14.47619047619047400000;
x2[61] = 14.98412698412698400000;
x2[62] = 15.49206349206349000000;
x2[63] = 16.00000000000000000000;


var y = new Array();
y[0] = +Infinity;
y[1] = 1664158979.11096290000000000000;
y[2] = 25596.98862206424700000000;
y[3] = 51.24224360332205900000;
y[4] = 0.80253721621001273000;
y[5] = 0.04013281604184240600;
y[6] = 0.00427181167466968250;
y[7] = 0.00077698684629307839;
y[8] = 0.00021140449751288852;
y[9] = 0.00007886641216275820;
y[10] = 0.00003797970495625904;
y[11] = 0.00002260186576944384;
y[12] = 0.00001608735704675994;
y[13] = 0.00001335526639440840;
y[14] = 0.00001267782407825002;
y[15] = 0.00001354410739307298;
y[16] = 0.00001607404700077214;
y[17] = 0.00002096489798949858;
y[18] = 0.00002978033411316872;
y[19] = 0.00004572015769326707;
y[20] = 0.00007536620884896827;
y[21] = 0.00013263967558882687;
y[22] = 0.00024800091950917796;
y[23] = 0.00049049578772052680;
y[24] = 0.00102225521238885490;
y[25] = 0.00223744147356661880;
y[26] = 0.00512739755878587920;
y[27] = 0.01226918030754863000;
y[28] = 0.03058049475427409400;
y[29] = 0.07921771472569966200;
y[30] = 0.21285098601167457000;
y[31] = 0.59211846233860321000;
y[32] = 1.70252376919407730000;
y[33] = 5.05197994186350920000;
y[34] = 15.44896866758827700000;
y[35] = 48.62279949816147700000;
y[36] = 157.31086033139039000000;
y[37] = 522.60021277476767000000;
y[38] = 1780.82316713426990000000;
y[39] = 6218.58509846337710000000;
y[40] = 22232.54916898025500000000;
y[41] = 81310.50695814844200000000;
y[42] = 303962.39599994919000000000;
y[43] = 1160609.39151835810000000000;
y[44] = 4523160.16396183520000000000;
y[45] = 17980506.53105686600000000000;
y[46] = 72861260.63140085300000000000;
y[47] = 300795965.18372804000000000000;
y[48] = 1264408843.88636260000000000000;
y[49] = 5408983705.82595920000000000000;
y[50] = 23536438485.32324600000000000000;
y[51] = 104125724201.77888000000000000000;
y[52] = 468137079409.17462000000000000000;
y[53] = 2137965865913.91260000000000000000;
y[54] = 9914368643808.25200000000000000000;
y[55] = 46665726995317.89800000000000000000;
y[56] = 222863786409039.87000000000000000000;
y[57] = 1079534443702065.00000000000000000000;
y[58] = 5302037850329952.00000000000000000000;
y[59] = 26394813313751084.00000000000000000000;
y[60] = 133146543235024720.00000000000000000000;
y[61] = 680375082351885950.00000000000000000000;
y[62] = 3520878542447823900.00000000000000000000;
y[63] = 18446744073709552000.00000000000000000000;



var val;
for (i = 0; i < vnum; i++)
{
	val = Math.pow(x1[i], x2[i]);
	if (!isEqual(val, y[i]))
	{
		$ERROR("\nx1 = " + x1[i] + "\nx2 = " + x2[i] + "\nlibc.pow(x1,x2) = " + y[i] + "\nMath.pow(x1,x2) = " + Math.pow(x1[i], x2[i]) + "\nMath.abs(libc.pow(x1,x2) - Math.pow(x1,x2)) > " + prec + "\n\n"); 
	}
}
// es5id: S15.8.2.13_A24
