// version: 1
#include "sp.h"

const char *sp_err2_str(int code)
{
	switch(code)
	{
	case SP_ERR_WR_ZERO: return "WR ZERO";
	case SP_ERR_WR_LESS: return "WR LESS";
	case SP_ERR_WR_LOCK: return "WR LOCK";
	case SP_ERR_WR_UNLOCK: return "WR UNLOCK";
	case SP_ERR_GET_MDM_STS: return "GET MDM STS";
	case SP_ERR_SET_MDM_STS: return "SET MDM STS";
	case SP_ERR_READ: return "READ";
	case SP_ERR_GET_OVERLAP: return "GET OVERLAP";
	case SP_ERR_WAIT_COMM_EVENT: return "WAIT COMM EVENT";
	case SP_ERR_PORT_NOT_EXIST: return "PORT NOT EXIST";
	case SP_ERR_PORT_OPEN_BUSY: return "PORT OPEN BUSY";
	case SP_ERR_PORT_OPEN: return "PORT OPEN";
	case SP_ERR_PORT_OPEN_INVALID: return "PORT_OPEN_INVALID";
	case SP_ERR_SET_TO: return "SET TO";
	case SP_ERR_GET_COMM_STATE: return "GET COMM STATE";
	case SP_ERR_SET_COMM_STATE: return "SET COMM STATE";
	case SP_ERR_SET_COMM_MASK: return "SET COMM MASK";
	case SP_ERR_CREATE_OVERLAP_OBJ: return "CREATE OVERLAP OBJ";
	case SP_ERR_CREATE_THREAD: return "CREATE THREAD";
	case SP_ERR_PARAM: return "PARAM";
	default: return "Unknown";
	}
}

#if defined(_WIN32)
#include <devguid.h>

int sp_enumerate(sp_list_t *list)
{
	if(!list->device_info_set || list->device_info_set == INVALID_HANDLE_VALUE)
	{
		list->device_info_set = SetupDiGetClassDevs(&GUID_DEVCLASS_PORTS, NULL, NULL, DIGCF_PRESENT);
		list->idx = 0;
		if(list->device_info_set == INVALID_HANDLE_VALUE) return 0;
	}
	SP_DEVINFO_DATA dev_info;
	dev_info.cbSize = sizeof(SP_DEVINFO_DATA);

	while(SetupDiEnumDeviceInfo(list->device_info_set, (DWORD)list->idx++, &dev_info))
	{
		HKEY hkey = SetupDiOpenDevRegKey(list->device_info_set, &dev_info, DICS_FLAG_GLOBAL, 0, DIREG_DEV, KEY_READ);

		list->info.port[0] = list->info.description[0] = list->info.hardware_id[0] = 0;

		TCHAR str[SP_INFO_LEN];
		DWORD str_len = SP_INFO_LEN;
		if(RegQueryValueEx(hkey, "PortName", NULL, NULL, (LPBYTE)str, &str_len) != EXIT_SUCCESS) continue;
		RegCloseKey(hkey);

		memcpy(list->info.port, str, str_len);
		// if(_tcsstr(port_name, L"LPT") != NULL) continue; // Ignore parallel ports

		if(SetupDiGetDeviceRegistryProperty(list->device_info_set, &dev_info, SPDRP_FRIENDLYNAME, NULL, (PBYTE)str, SP_INFO_LEN, &str_len))
			memcpy(list->info.description, str, str_len);
		if(SetupDiGetDeviceRegistryProperty(list->device_info_set, &dev_info, SPDRP_HARDWAREID, NULL, (PBYTE)str, SP_INFO_LEN, &str_len))
			memcpy(list->info.hardware_id, str, str_len);
		return 1;
	}

	SetupDiDestroyDeviceInfoList(list->device_info_set);
	list->device_info_set = 0;

	return 0;
}

void sp_enumerate_finish(sp_list_t *list)
{
	SetupDiDestroyDeviceInfoList(list->device_info_set);
	list->device_info_set = 0;
}
#endif

#if defined(__linux__) || defined(__CYGWIN__)
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

static bool path_exists(const char *path)
{
	struct stat sb;
	return stat(path, &sb) == 0;
}

static void read_line(char *s, const char *path)
{
	FILE *f = fopen(path, "r");
	if(f == NULL) return;
	char *line = NULL;
	size_t len = 0;
	ssize_t readed = getline(&line, &len, f);
	if(readed > 1)
	{
		memcpy(s, line, readed - 1);
		s[readed - 1] = 0;
	}
	if(line) free(line);
	fclose(f);
}

static int realpath_(char *real_path, const char *path) { return realpath(path, real_path) ? 0 : 1; }

static void dirname(char *dst, const char *src)
{
	int len = strlen(src);
	dst[0] = 0;
	for(int i = len - 1; i >= 1; i--)
	{
		char *e = strchr(src + i, '/');
		if(e)
		{
			memcpy(dst, src, e - src);
			dst[e - src] = 0;
			return;
		}
	}
}

static void to_upper(char *temp)
{
	char *name = strtok(temp, ":");
	char *s = name;
	if(*temp)
		while(*s)
		{
			*s = toupper((unsigned char)*s);
			s++;
		}
}

static void usb_sysfs_fields(char *name, char *hw, const char *sysfs_path)
{
	char mf[SP_INFO_LEN] = {0}, prod[SP_INFO_LEN] = {0}, vid[SP_INFO_LEN] = {0}, pid[SP_INFO_LEN] = {0}, ser[SP_INFO_LEN] = {0}, tmp[SP_INFO_LEN];

#define GET_FIELD(f)
	snprintf(tmp, sizeof(tmp), "%s/manufacturer", sysfs_path);
	read_line(mf, tmp);
	snprintf(tmp, sizeof(tmp), "%s/product", sysfs_path);
	read_line(prod, tmp);
	snprintf(tmp, sizeof(tmp), "%s/serial", sysfs_path);
	read_line(ser, tmp);
	snprintf(tmp, sizeof(tmp), "%s/idVendor", sysfs_path);
	read_line(vid, tmp);
	snprintf(tmp, sizeof(tmp), "%s/idProduct", sysfs_path);
	read_line(pid, tmp);

	int len = 0;
	if(*mf) len += sprintf(name, "%s", mf);
	if(*prod) sprintf(&name[len], len > 0 ? "::%s" : "%s", prod);

	len = 0;
	to_upper(vid);
	to_upper(pid);
	if(*vid && *pid) len += sprintf(&hw[len], "VID_%s&PID_%s", vid, pid);
	if(*ser) sprintf(&hw[len], len > 0 ? "&SN_%s" : "SN_%s", ser);
}

static void _basename(char *dst, const char *src)
{
	int len = strlen(src);
	dst[0] = 0;
	for(int i = len - 1; i >= 1; i--)
	{
		char *e = strchr(src + i, '/');
		if(e)
		{
			strcpy(dst, e + 1);
			return;
		}
	}
}

static int strncmp2(const char *s, const char *s_pattern)
{
	size_t len_s = strlen(s), len_pattern = strlen(s_pattern);
	if(len_s < len_pattern) return len_pattern - len_s;
	return strncmp(s, s_pattern, len_pattern);
}

static const char *search_sources[] = {
	"/dev/ttyACM*",
	"/dev/ttyS*",
	"/dev/ttyUSB*",
	"/dev/tty.*",
	"/dev/cu.*",
};

void sp_enumerate_finish(sp_list_t *list)
{
	globfree(&list->globbuf);
	list->inited = false;
}

int sp_enumerate(sp_list_t *list)
{
	if(!list->inited)
	{
		glob(search_sources[0], 0, NULL, &list->globbuf);
		for(size_t i = 1; i < sizeof(search_sources) / sizeof(search_sources[0]); i++)
			glob(search_sources[i], GLOB_APPEND, NULL, &list->globbuf);
		list->idx = 0;
		list->inited = true;
	}
	while(list->idx < list->globbuf.gl_pathc)
	{
		list->info.port[0] = list->info.description[0] = list->info.hardware_id[0] = 0;

		char device_name[SP_INFO_LEN], sys_device_path[SP_INFO_LEN + 22];
		_basename(device_name, list->globbuf.gl_pathv[list->idx]);
		snprintf(sys_device_path, sizeof(sys_device_path), "/sys/class/tty/%s/device", device_name);
		sprintf(list->info.port, "%s", list->globbuf.gl_pathv[list->idx]);

		if(strncmp2(device_name, "ttyUSB") == 0)
		{
			char real_path[SP_INFO_LEN];
			if(realpath_(real_path, sys_device_path) == 0)
			{
				char path2[SP_INFO_LEN];
				dirname(path2, real_path);
				dirname(sys_device_path, path2);
				if(path_exists(sys_device_path)) usb_sysfs_fields(list->info.description, list->info.hardware_id, sys_device_path);
			}
		}
		else if(strncmp2(device_name, "ttyACM") == 0)
		{
			char real_path[SP_INFO_LEN];
			if(realpath_(real_path, sys_device_path) == 0)
			{
				dirname(sys_device_path, real_path);
				if(path_exists(sys_device_path)) usb_sysfs_fields(list->info.description, list->info.hardware_id, sys_device_path);
			}
		}
		else
		{
			char sys_id_path[SP_INFO_LEN + 25];
			snprintf(sys_id_path, sizeof(sys_id_path), "%s/id", sys_device_path);
			if(path_exists(sys_id_path)) read_line(list->info.hardware_id, sys_id_path);
		}

		list->idx++;
		return 1;
	}
	globfree(&list->globbuf);
	list->inited = false;
	return 0;
}
#endif