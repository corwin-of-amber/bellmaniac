name := "bellmaniac"

version := "0.1"

scalaVersion := "2.11.12"

libraryDependencies += "org.scala-lang" % "scala-library" % "2.11.12"
libraryDependencies += "org.mongodb" % "mongo-java-driver" % "2.13.1"
libraryDependencies += "org.rogach" %% "scallop" % "0.9.5"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.0" % Test
libraryDependencies += "junit" % "junit" % "4.13-beta-1"

unmanagedJars in Compile += file("lib/com.microsoft.z3.jar")

excludeFilter in unmanagedSources := HiddenFileFilter || "*SynthSCP*"