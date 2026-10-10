/-
# CountingMatroidTest

Tests that are not theorems: the planted breaches that make the build-time
checkers falsifiable. Kept out of `CountingMatroid` so that the library a client
imports carries no deliberately-broken declarations.
-/

import CountingMatroidTest.CostSealBreaches
import CountingMatroidTest.CostSealExchange
import CountingMatroidTest.CostSealNoncomputable
import CountingMatroidTest.CostSealCasesOn
import CountingMatroidTest.CostSealHandPriced
import CountingMatroidTest.CostSealCost
import CountingMatroidTest.CostSealTransitive
import CountingMatroidTest.CostSealMeasure
import CountingMatroidTest.CostSealPeakAt
