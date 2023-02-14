val scala3Version = "3.2.2"

resolvers += Resolver.mavenLocal
val jarName = "CircAG.jar"
assembly/assemblyJarName := jarName

lazy val root = project
  .in(file("."))
  .settings(
    name := "circAG",
    version := "0.1",

    scalaVersion := scala3Version,
    libraryDependencies ++= Seq("org.scalameta" %% "munit" % "0.7.29" % Test,
    	"org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1",
	// libraryDependencies += "net.sourceforge.htmlcleaner" % "htmlcleaner" % "2.2"
	// https://mvnrepository.com/artifact/de.learnlib/learnlib-api
		"de.learnlib" % "learnlib-api" % "0.16.0",
	// https://mvnrepository.com/artifact/de.learnlib/learnlib-parent
	// libraryDependencies += "de.learnlib" % "learnlib-parent" % "0.16.0"
	// https://mvnrepository.com/artifact/de.learnlib/learnlib-parent
		"de.learnlib" % "learnlib-parent" % "0.16.0" pomOnly(),
		"de.learnlib.distribution" % "learnlib-distribution" % "0.16.0" pomOnly(),
		"net.automatalib" % "automata-core" % "0.10.0",
		"com.github.scopt" %% "scopt" % "4.0.1",
		"org.slf4j" % "slf4j-api" % "1.7.9",
        "org.slf4j" % "slf4j-simple" % "1.7.9"
  		)
  	)
cancelable in Global := true

// lazy val root = project
//   .in(file("."))
//   .settings(
//     name := "circAG",
//     version := "0.1.0-SNAPSHOT",

//     scalaVersion := scala3Version,

//     libraryDependencies += "org.scalameta" %% "munit" % "0.7.29" % Test
//   )
