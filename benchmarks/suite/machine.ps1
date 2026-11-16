param(
    [ValidateSet('Snapshot','Monitor')][string]$Action = 'Snapshot',
    [int]$Cpu = 2, [int]$ProcessId = 0,
    [string]$OutputPath, [string]$StopFile, [double]$IntervalSeconds = 1
)
$ErrorActionPreference = 'Stop'
$encoding = [System.Text.UTF8Encoding]::new($false)
[Console]::OutputEncoding = $encoding
Add-Type -TypeDefinition @"
using System;
using System.Runtime.InteropServices;
[StructLayout(LayoutKind.Sequential)]
public struct BenchPowerState {
    public byte ACLineStatus, BatteryFlag, BatteryLifePercent, SystemStatusFlag;
    public uint BatteryLifeTime, BatteryFullLifeTime;
}
public static class BenchPowerApi {
    [DllImport("kernel32.dll")]
    [return: MarshalAs(UnmanagedType.Bool)]
    public static extern bool GetSystemPowerStatus(out BenchPowerState state);
}
"@
function Read-BenchPower {
    $state = [BenchPowerState]::new()
    if ([BenchPowerApi]::GetSystemPowerStatus([ref]$state)) { return $state }
    return $null
}
if ($Action -eq 'Snapshot') {
    $processors = @(Get-CimInstance Win32_Processor | Select-Object Name,Manufacturer,NumberOfCores,NumberOfLogicalProcessors,MaxClockSpeed,CurrentClockSpeed,L2CacheSize,L3CacheSize)
    $system = Get-CimInstance Win32_ComputerSystem
    $os = Get-CimInstance Win32_OperatingSystem
    $bios = Get-CimInstance Win32_BIOS
    $memory = @(Get-CimInstance Win32_PhysicalMemory | Select-Object Capacity,Speed,ConfiguredClockSpeed)
    $power = (& powercfg.exe /getactivescheme | Out-String).Trim()
    $processorPolicy = (& powercfg.exe /qh SCHEME_CURRENT SUB_PROCESSOR | Out-String).Trim()
    if ($LASTEXITCODE -ne 0) { throw 'Could not read processor power policy' }
    $supply = Read-BenchPower
    [ordered]@{
        captured_utc = [DateTime]::UtcNow.ToString('o')
        processors = $processors
        memory_bytes = $system.TotalPhysicalMemory
        memory_modules = $memory
        os_caption = $os.Caption
        os_version = $os.Version
        os_build = $os.BuildNumber
        bios_version = $bios.SMBIOSBIOSVersion
        power_scheme = $power
        processor_power_policy = $processorPolicy
        ac_line_status = if ($supply) { $supply.ACLineStatus } else { $null }
        battery_flag = if ($supply) { $supply.BatteryFlag } else { $null }
        logical_cpu = $Cpu
        frequency_note = 'WMI clocks are OS-reported MHz and may be nominal or stale. They are not hardware effective-clock measurements.'
    } | ConvertTo-Json -Depth 8
    exit 0
}
if (!$OutputPath -or !$StopFile -or !$ProcessId) { throw 'Monitor needs OutputPath, StopFile and ProcessId' }
$stream = [System.IO.StreamWriter]::new($OutputPath, $false, $encoding)
try {
    while (!(Test-Path -LiteralPath $StopFile)) {
        $record = [ordered]@{ utc = [DateTime]::UtcNow.ToString('o'); logical_cpu = $Cpu }
        try {
            $counter = Get-CimInstance Win32_PerfFormattedData_Counters_ProcessorInformation -Filter "Name='0,$Cpu'"
            if (!$counter) { throw 'Per-CPU counters unavailable' }
            $record.reported_frequency_mhz = $counter.ProcessorFrequency
            $record.percent_processor_performance = $counter.PercentProcessorPerformance
            $record.percent_processor_time = $counter.PercentProcessorTime
        } catch { $record.counter_error = $_.Exception.Message }
        $supply = Read-BenchPower
        if ($supply) { $record.ac_line_status = $supply.ACLineStatus }
        try {
            $process = Get-Process -Id $ProcessId -ErrorAction Stop
            $record.working_set_bytes = $process.WorkingSet64
            $record.process_cpu_seconds = $process.TotalProcessorTime.TotalSeconds
        } catch { $record.process_error = $_.Exception.Message }
        $stream.WriteLine(($record | ConvertTo-Json -Compress -Depth 5))
        $stream.Flush()
        Start-Sleep -Milliseconds ([int]($IntervalSeconds * 1000))
    }
} finally { $stream.Dispose() }
