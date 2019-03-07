lazy val root = project
  .in(file("."))
  .settings(
    name := "polyparse",
    version := "0.1.0",

    scalaVersion := dottyLatestNightlyBuild.get,
)

