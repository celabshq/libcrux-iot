-- Library root: with the lakefile glob removed, this module's import tree is
-- what `lake build` compiles. Import the import-DAG sinks so every real proof
-- module is reached (`Verification.ProofObligations` imports `Sponge.Shake`, which
-- imports the whole proof); the generated `Extraction.ProofObligations` (sorries) is
-- deliberately NOT imported, so it stays on disk but out of the build.
import LibcruxIotSha3.Extraction
import LibcruxIotSha3.Verification.ProofObligations
import LibcruxIotSha3.Composition.Pedantic.Chi
import LibcruxIotSha3.Composition.Pedantic.Pi
import LibcruxIotSha3.Composition.Pedantic.Theta
import LibcruxIotSha3.Composition.Pedantic.Rho
import LibcruxIotSha3.Composition.Pedantic.Iota
import LibcruxIotSha3.Composition.Pedantic.RoundConstants
import LibcruxIotSha3.Composition.Pedantic.Round
import LibcruxIotSha3.Composition.Pedantic.Permutation
import LibcruxIotSha3.Composition.Pedantic.Bits
import LibcruxIotSha3.Composition.Pedantic.KeccakP
import LibcruxIotSha3.Composition.Pedantic.BitsOps
import LibcruxIotSha3.Composition.Pedantic.Padding
import LibcruxIotSha3.Composition.Pedantic.Sponge
import LibcruxIotSha3.Composition.Pedantic.KeccakC
import LibcruxIotSha3.Composition.Pedantic.Sha3
import LibcruxIotSha3.Composition.LaneBridge
import LibcruxIotSha3.Composition.Pedantic.Lanes
import LibcruxIotSha3.Composition.Pedantic.LaneSponge
import LibcruxIotSha3.Composition.Pedantic.LaneAbsorb
import LibcruxIotSha3.Composition.Pedantic.LaneSqueeze
import LibcruxIotSha3.Composition.Pedantic.Bytes
