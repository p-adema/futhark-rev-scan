-- Does the acos64 function work?
-- ==
-- input { 1f64 } output { 0f64 }
-- input { 0.5403023f64 } output { 1f64 }
-- input { -1f64 } output { 3.1415927f64 }

import "futlib/numeric"

fun main(x: f64): f64 = F64.acos(x)
