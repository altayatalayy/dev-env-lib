//! Adapts protocol package lists to the host package-manager implementation
//! shared with release installers.

const std = @import("std");
const shared = @import("shared");
const proto = shared.protocol;
const platform = shared.platform;

pub const InstallResult = struct {
    installed: []const []const u8 = &.{},

    pub fn changed(r: InstallResult) bool {
        return r.installed.len > 0;
    }
};

pub const Manager = struct {
    package_manager: platform.PackageManager,

    pub fn init(pm: platform.PackageManager) Manager {
        return .{ .package_manager = pm };
    }

    pub fn ensureInstalled(
        m: Manager,
        alloc: std.mem.Allocator,
        io: std.Io,
        packages: proto.SystemPackages,
    ) !InstallResult {
        const installed = try m.package_manager.install(alloc, io, packages.apt, .{});
        return .{ .installed = installed };
    }
};

// --- tests ---

test "manager selects its own package lists" {
    // Empty lists are a no-op for apt; this exercises dispatch
    // without touching the host system.
    const packages: proto.SystemPackages = .{};
    const io = std.testing.io;
    const apt_result = try Manager.init(.init(.apt)).ensureInstalled(std.testing.allocator, io, packages);
    try std.testing.expect(!apt_result.changed());
}
