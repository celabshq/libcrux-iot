-- Library root: with the lakefile glob removed, this module's import tree is
-- what `lake build` compiles. Import the import-DAG sinks so every real proof
-- module is reached (`Verification.ProofObligations` imports `Sponge.Shake`, which
-- imports the whole proof); the generated `Extraction.ProofObligations` (sorries) is
-- deliberately NOT imported, so it stays on disk but out of the build.
import LibcruxIotSha3.Extraction.Funs
import LibcruxIotSha3.Verification.ProofObligations
import HacspecSha3
