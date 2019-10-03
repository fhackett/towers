
lazy val latestDotty = dottyLatestNightlyBuild.get

ThisBuild / version := "0.1.0"
ThisBuild / scalaVersion := latestDotty

lazy val core = project
  .in(file("."))
  .settings(
    name := "towers")

lazy val testing = project
  .in(file("testing"))
  .aggregate(core)
  .dependsOn(core)
  .settings(
    name := "towers-testing",
    libraryDependencies += "com.novocode" % "junit-interface" % "0.11" % "test")

