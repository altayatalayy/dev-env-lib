//! Typed API of this installer release. main.zig adapts JSON commands to
//! these calls; everything below this point works on Zig types only.

const std = @import("std");
const shared = @import("shared");
const proto = shared.protocol;
const platform = shared.platform;
const release = @import("environment_release");
const planner = @import("planner.zig");
const apply_mod = @import("apply.zig");
const verify_mod = @import("verify.zig");
const uninstall_mod = @import("uninstall.zig");
const dotfiles_mod = @import("dotfiles.zig");
const layout_mod = @import("layout.zig");
const progress_mod = @import("progress.zig");

pub const Env = struct {
    home: []const u8,
    environ_map: *std.process.Environ.Map,

    fn toApplyEnv(
        env: Env,
        requested: proto.InstallLayout,
    ) !apply_mod.Env {
        return .{
            .layout = try layout_mod.Layout.init(env.home, requested),
            .environ_map = env.environ_map,
        };
    }
};

pub const Progress = progress_mod.Progress;

fn checkPlatform(p: platform.Platform) error{UnsupportedPlatform}!void {
    if (!std.mem.eql(u8, p.fields().version, "24.04") or !release.supportsPlatform(p)) {
        return error.UnsupportedPlatform;
    }
}

pub fn metadata(alloc: std.mem.Allocator) !proto.MetadataResponse {
    var tool_infos: std.ArrayList(proto.ToolInfo) = .empty;
    for (release.tool_defs) |def| {
        try tool_infos.append(alloc, .{
            .name = @tagName(def.id),
            .description = def.description,
            .platforms = def.platforms,
        });
    }

    var config_infos: std.ArrayList(proto.ConfigInfo) = .empty;
    for (release.tool_defs) |tool| {
        for (tool.configs) |def| {
            try config_infos.append(alloc, .{
                .name = @tagName(def.id),
                .configures = @tagName(def.for_tool),
            });
        }
    }

    return .{
        .protocol = proto.version,
        .release = release.name,
        .platforms = try release.supportedPlatforms(alloc),
        .tools = tool_infos.items,
        .configs = config_infos.items,
    };
}

pub fn resolve(alloc: std.mem.Allocator, progress: ?*Progress, req: proto.ResolveRequest) !proto.ResolveResponse {
    try checkPlatform(req.platform);
    const response = try planner.resolve(alloc, req);
    if (progress) |p| {
        try p.emit(.{ .event = "graph_built", .tools = response.resolved_tools });
        try p.emit(.{ .event = "resolution_ready", .tools = response.resolved_tools, .packages = response.stow_packages });
    }
    return response;
}

pub fn apply(
    alloc: std.mem.Allocator,
    io: std.Io,
    env: Env,
    progress: ?*Progress,
    req: proto.ApplyRequest,
) !proto.ApplyResponse {
    try checkPlatform(req.platform);
    return apply_mod.apply(alloc, io, try env.toApplyEnv(req.layout), progress, release.defs, req);
}

pub fn verify(
    alloc: std.mem.Allocator,
    io: std.Io,
    env: Env,
    progress: ?*Progress,
    req: proto.VerifyRequest,
) !proto.VerifyResponse {
    try checkPlatform(req.platform);
    return verify_mod.verify(alloc, io, try env.toApplyEnv(req.layout), progress, release.defs, req);
}

pub fn applyConfigs(
    alloc: std.mem.Allocator,
    io: std.Io,
    env: Env,
    progress: ?*Progress,
    req: proto.ConfigApplyRequest,
) !proto.ConfigApplyResponse {
    try checkPlatform(req.platform);
    return apply_mod.applyConfigs(alloc, io, try env.toApplyEnv(req.layout), progress, release.defs, req);
}

pub fn uninstall(
    alloc: std.mem.Allocator,
    io: std.Io,
    env: Env,
    progress: ?*Progress,
    req: proto.UninstallRequest,
) !proto.UninstallResponse {
    try checkPlatform(req.platform);
    return uninstall_mod.uninstall(alloc, io, try env.toApplyEnv(req.layout), progress, release.defs, req);
}

pub fn extractDotfiles(
    alloc: std.mem.Allocator,
    io: std.Io,
    progress: ?*Progress,
    req: proto.ExtractDotfilesRequest,
) !proto.ExtractDotfilesResponse {
    if (!std.fs.path.isAbsolute(req.dest)) return error.DestNotAbsolute;
    if (progress) |p| try p.emit(.{ .event = "config_apply_started", .detail = "extract dotfiles" });
    const packages = try dotfiles_mod.extract(alloc, io, req.dest);
    if (progress) |p| try p.emit(.{ .event = "config_apply_finished", .packages = packages });
    return .{ .packages = packages };
}

// --- tests ---

test metadata {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const alloc = arena_state.allocator();

    const meta = try metadata(alloc);
    try std.testing.expectEqual(proto.version, meta.protocol);
    try std.testing.expectEqualStrings(release.name, meta.release);
    try std.testing.expectEqual(release.tool_defs.len, meta.tools.len);
    try std.testing.expectEqual(countConfigs(), meta.configs.len);
    try std.testing.expect(meta.platforms.len > 0);
    for (meta.tools) |tool| {
        try std.testing.expect(tool.platforms.len > 0);
    }

    // Release data must form a valid dependency graph.
    try @import("installer_resolver").validate(alloc, release.defs);
}

fn countConfigs() usize {
    var count: usize = 0;
    for (release.tool_defs) |tool| count += tool.configs.len;
    return count;
}

test "unsupported platform is a hard error" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const alloc = arena_state.allocator();

    // Only the declared Ubuntu version is supported.
    try std.testing.expectError(error.UnsupportedPlatform, resolve(alloc, null, .{
        .protocol = proto.version,
        .platform = .{ .ubuntu = .{ .version = "22.04", .arch = .x86_64 } },
        .tools = &.{},
        .include_configs = true,
    }));
}
