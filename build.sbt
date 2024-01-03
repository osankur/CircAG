val scala3Version = "3.3.1"

resolvers += Resolver.mavenLocal
resolvers += "artemis" at "https://artifacts.itemis.cloud/repository/maven-mps"
resolvers += "mvrep" at "https://repo1.maven.org/maven2/"

val jarName = "CircAG.jar"
assembly/assemblyJarName := jarName
assembly / mainClass := Some("fr.irisa.circag.Main")
lazy val root = project
  .in(file("."))
  .settings(
    name := "circAG",
    version := "0.1",
    scalaVersion := scala3Version,
    libraryDependencies ++= Seq("org.scalameta" %% "munit" % "0.7.29" % Test,
		// "org.sosy-lab" %% "java-smt" % "3.14.3" from "https://repo1.maven.org/maven2/org/sosy-lab/java-smt/3.14.3/java-smt-3.14.3.jar",
		// "org.sosy-lab" %% "common" % "0.3000-529-g6152d88" from "https://repo1.maven.org/maven2/org/sosy-lab/common/0.3000-529-g6152d88/common-0.3000-529-g6152d88.jar",
		// "de.uni-freiburg.informatik.ultimate" %% "smtinterpol" % "2.5-1242-g5c50fb6d" from "https://repo1.maven.org/maven2/de/uni-freiburg/informatik/ultimate/smtinterpol/2.5-1242-g5c50fb6d/smtinterpol-2.5-1242-g5c50fb6d.jar",
    	"org.scala-lang.modules" %% "scala-parser-combinators" % "2.2.0",
		"de.learnlib" % "learnlib-api" % "0.16.0",
		"de.learnlib" % "learnlib-parent" % "0.16.0" pomOnly(),
		"de.learnlib.distribution" % "learnlib-distribution" % "0.16.0" pomOnly(),
		"dk.brics" % "automaton" % "1.12-4",
		"net.automatalib" % "automata-core" % "0.10.0",
		"com.github.scopt" %% "scopt" % "4.1.0",
		"org.slf4j" % "slf4j-api" % "1.7.9",
        "org.slf4j" % "slf4j-simple" % "1.7.9",
		"tools.aqua" % "z3-turnkey" % "4.11.2",
		"jhoafparser" % "jhoafparser" % "1.1.1"
  		)
  	)
cancelable in Global := true


envVars += ("org.slf4j.simpleLogger.defaultLogLevel" -> "debug")
ThisBuild / assemblyMergeStrategy := {
  case PathList("META-INF", x, xs @ _*) if x.toLowerCase == "services" => MergeStrategy.filterDistinctLines
  case PathList("META-INF", xs @ _*) => MergeStrategy.discard
  case x => MergeStrategy.first
}