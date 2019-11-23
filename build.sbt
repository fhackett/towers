
lazy val latestDotty = dottyLatestNightlyBuild.get

ThisBuild / version := "0.1.0"
ThisBuild / scalaVersion := latestDotty

lazy val core = project
  .in(file("."))
  .settings(
    name := "towers",
    scalacOptions += "-Yretain-trees", // allow inspecting *Def bodies via Symbol, otherwise definitions come back with empty
                                       // bodies
    libraryDependencies += "com.novocode" % "junit-interface" % "0.11" % "test")

