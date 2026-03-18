
/-
module m1.ep
----------------
let x = 1

module m2.ep
---------------
import m1 : M1
let y = m1.x

module m3.ep
----------------
import m1 : M1; m2 : M2
let z = m1.x + m2.y


temp = link(m1, m2)  
result = link(temp, m3).x


function f {..};;
function g {..};
x = f;
x = g
-/
