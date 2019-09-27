
lazy val latestDotty = dottyLatestNightlyBuild.get

lazy val root = project
  .in(file("."))
  .settings(
    name := "towers",
    version := "0.1.0",

    scalaVersion := /*"0.19.0-RC1",*/ latestDotty,
)

