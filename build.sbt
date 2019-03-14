
lazy val latestDotty = dottyLatestNightlyBuild.get

lazy val root = project
  .in(file("."))
  .settings(
    name := "polyparse",
    version := "0.1.0",

    scalaVersion := latestDotty,
    //scalacOptions += "-with-compiler",
    libraryDependencies ++= Seq(
        "ch.epfl.lamp" %% "dotty-compiler" % latestDotty,
        "ch.epfl.lamp" % "dotty-interfaces" % latestDotty,
        "org.scala-lang.modules" % "scala-asm" % "6.0.0-scala-1",
    ),
)

