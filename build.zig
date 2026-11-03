const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const cli = b.dependency("zig_cli", .{
        .target = target,
        .optimize = optimize,
    }).module("cli");
    const graph = b.dependency("zig_graph", .{
        .target = target,
        .optimize = optimize,
    }).module("graph");

    const shared = b.addModule("shared", .{
        .root_source_file = b.path("src/shared/shared.zig"),
        .target = target,
        .optimize = optimize,
    });
    const tools = b.addModule("installer_tools", .{
        .root_source_file = b.path("src/installer/tools.zig"),
        .target = target,
        .optimize = optimize,
    });
    tools.addImport("shared", shared);

    const resolver = b.addModule("installer_resolver", .{
        .root_source_file = b.path("src/installer/resolver.zig"),
        .target = target,
        .optimize = optimize,
    });
    resolver.addImport("shared", shared);
    resolver.addImport("graph", graph);
    resolver.addImport("installer_tools", tools);

    const installer = b.addModule("installer", .{
        .root_source_file = b.path("src/installer/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    installer.addImport("shared", shared);
    installer.addImport("installer_tools", tools);
    installer.addImport("installer_resolver", resolver);

    const frontend = b.addModule("frontend", .{
        .root_source_file = b.path("src/dev_env/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    frontend.addImport("shared", shared);
    frontend.addImport("cli", cli);
    b.installArtifact(b.addExecutable(.{ .name = "dev-env", .root_module = frontend }));

    const tests = b.step("test", "Run generic unit tests");
    tests.dependOn(&b.addRunArtifact(b.addTest(.{ .root_module = shared })).step);
    tests.dependOn(&b.addRunArtifact(b.addTest(.{ .root_module = frontend })).step);

    const fixture_ids = b.createModule(.{
        .root_source_file = b.path("test/fixture_ids.zig"),
        .target = target,
        .optimize = optimize,
    });
    const test_tools = b.createModule(.{
        .root_source_file = b.path("src/installer/tools.zig"),
        .target = target,
        .optimize = optimize,
    });
    test_tools.addImport("shared", shared);
    test_tools.addImport("environment_ids", fixture_ids);
    const test_resolver = b.createModule(.{
        .root_source_file = b.path("src/installer/resolver.zig"),
        .target = target,
        .optimize = optimize,
    });
    test_resolver.addImport("shared", shared);
    test_resolver.addImport("graph", graph);
    test_resolver.addImport("installer_tools", test_tools);
    tests.dependOn(&b.addRunArtifact(b.addTest(.{ .root_module = test_tools })).step);
    tests.dependOn(&b.addRunArtifact(b.addTest(.{ .root_module = test_resolver })).step);
}
