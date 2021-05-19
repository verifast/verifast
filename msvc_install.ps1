param(
    [ValidateNotNullOrEmpty()][System.IO.FileInfo]$install_dir = "C:\vfMSVC"
)

$msvc_installer_link = "https://download.visualstudio.microsoft.com/download/pr/22c17f05-944c-48dc-9f68-b1663f9df4cb/2492827d2bc58c5cd0a4e4ab40da86910d05ee96f71d69b561457885b3249a91/vs_Community.exe"
$msvc_installer_exe = "msvc_installer.exe"

Invoke-WebRequest -Uri $msvc_installer_link -OutFile $msvc_installer_exe

$workloads = [String]::Join(" ",(
        @(
            "Microsoft.VisualStudio.Workload.NativeDesktop"
            "Microsoft.VisualStudio.Component.VC.CMake.Project"
            "Microsoft.VisualStudio.Component.Windows10SDK.19041"
            "Microsoft.VisualStudio.Component.VC.Tools.x86.x64"
        ) | ForEach-Object { "--add " + $_ }
    )
)

$options = [String]::Join(" ",(
        @(
            "passive"
            "norestart"
        ) | ForEach-Object { "--" + $_ }
    )
)

$msvc_installation = Start-Process -NoNewWindow -FilePath "$msvc_installer_exe" -ArgumentList "--installPath $install_dir $workloads $options" -Wait -PassThru
$msvc_ec = $msvc_installation.ExitCode

if ($msvc_ec -eq 3010) {
    Write-Host "The installation of MSVC required a reboot. Please reboot your machine."
} elseif ($msvc_ec -eq 0) {
    Remove-Item $msvc_installer_exe
    Write-Host "Installation completed successfully"
} else {
    Write-Host "Installation exited with error code $msvc_ec. See https://docs.microsoft.com/en-us/visualstudio/install/use-command-line-parameters-to-install-visual-studio?view=vs-2019#error-codes"
}