/*
	Based up Neutrino-GUI - Tuxbox-Project
	Copyright (C) 2001 by Steffen Hehn 'McClean'

	OPKG-Manager Class for Neutrino-GUI

	Implementation:
	Copyright (C) 2012-2014 T. Graf 'dbt'
	www.dbox2-tuning.net

	Adaptions:
	Copyright (C) 2013 martii
	gitorious.org/neutrino-mp/martiis-neutrino-mp
	Copyright (C) 2015 Stefan Seyfried

	License: GPL

	This program is free software; you can redistribute it and/or
	modify it under the terms of the GNU General Public
	License as published by the Free Software Foundation; either
	version 2 of the License, or (at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
	General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with this program. If not, see <http://www.gnu.org/licenses/>.
*/

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <gui/opkg_manager.h>

#include <global.h>
#include <neutrino.h>
#include <neutrino_menue.h>

#include <gui/widget/icons.h>
#include <gui/widget/messagebox.h>
#include <gui/widget/shellwindow.h>
#include <gui/widget/progresswindow.h>
#include <driver/screen_max.h>
#include <gui/filebrowser.h>
#include <system/debug.h>
#include <system/helpers.h>
#include <unistd.h>
#include <sys/vfs.h>
#include <poll.h>
#include <fcntl.h>
#include <alloca.h>
#include <errno.h>
/* later this can be changed to just "opkg" */
#define OPKG_CL "opkg-cl"
#define OPKG_CL_CONFIG_OPTIONS " -V2 --tmp-dir=/tmp --cache=/tmp/.opkg "

using namespace std;

enum
{
	OM_LIST,
	OM_LIST_INSTALLED,
	OM_LIST_UPGRADEABLE,
	OM_UPDATE,
	OM_UPGRADE,
	OM_REMOVE,
	OM_INFO,
	OM_INSTALL,
	OM_STATUS,
	OM_MAX
};

static const string pkg_types[OM_MAX] =
{
	OPKG_CL " list ",
	OPKG_CL " list-installed ",
	OPKG_CL " list-upgradable ",
	OPKG_CL " -A update ",
	OPKG_CL OPKG_CL_CONFIG_OPTIONS " upgrade ",
	OPKG_CL OPKG_CL_CONFIG_OPTIONS " remove ",
	OPKG_CL " info ",
	OPKG_CL OPKG_CL_CONFIG_OPTIONS " install ",
	OPKG_CL " status ",
};

COPKGManager::COPKGManager()
{
	width = 80;
	pkg_map.clear();
	list_installed_done = false;
	list_upgradeable_done = false;
	expert_mode = false;
	local_dir = &g_settings.update_dir_opkg;
	CFileHelpers::createDir("/tmp/.opkg");
}

COPKGManager::~COPKGManager()
{
}

int COPKGManager::exec(CMenuTarget* parent, const string &actionKey)
{
	int res = menu_return::RETURN_REPAINT;

	if (actionKey.empty()) {
		if (parent)
			parent->hide();
		return showMenu();
	}
	int selected = menu->getSelected() - menu_offset;

	if (expert_mode && actionKey == "rc_blue") {
		if (selected < 0 || selected >= (int) pkg_vec.size() || !pkg_vec[selected]->installed)
			return menu_return::RETURN_NONE;

		char loc[200];
		snprintf(loc, sizeof(loc), g_Locale->getText(LOCALE_OPKG_MESSAGEBOX_REMOVE), pkg_vec[selected]->name.c_str());
		if (ShowMsg(LOCALE_OPKG_TITLE, loc, CMessageBox::mbrCancel, CMessageBox::mbYes | CMessageBox::mbCancel) != CMessageBox::mbrCancel) {
			if (parent)
				parent->hide();
			execCmd(pkg_types[OM_REMOVE] + pkg_vec[selected]->name, true, true);
			refreshMenu();
		}
		return res;
	}
	if (actionKey == "rc_info") {
		if (selected < 0 || selected >= (int) pkg_vec.size())
			return menu_return::RETURN_NONE;
		if (parent)
			parent->hide();
		execCmd(pkg_types[OM_INFO] + pkg_vec[selected]->name, true, true);
		return res;
	}
	if (actionKey == "rc_yellow") {
		expert_mode = !expert_mode;
		updateMenu();
		return res;
	}
	if (actionKey == "local_package") {
		if (parent)
			parent->hide();

		CFileFilter fileFilter;
		string filters[] = {"opk", "ipk"};
		for(size_t i=0; i<sizeof(filters)/sizeof(filters[0]) ;i++)
			fileFilter.addFilter(filters[i]);

		CFileBrowser fileBrowser;
		fileBrowser.Filter = &fileFilter;

		if (fileBrowser.exec((*local_dir).c_str()))
		{
			string pkg_name = fileBrowser.getSelectedFile()->Name;
			if (!installPackage(pkg_name))
				showError(g_Locale->getText(LOCALE_OPKG_FAILURE_INSTALL), strerror(errno), pkg_name);

			*local_dir = fileBrowser.getCurrentDir();
		refreshMenu();
		}
		return res;
	}
	if(actionKey == pkg_types[OM_UPGRADE]) {
		if (parent)
			parent->hide();
		int r = execCmd(actionKey, true, true);
		if (r) {
			showError(g_Locale->getText(LOCALE_OPKG_FAILURE_UPGRADE), strerror(errno), actionKey);
		} else
			installed = true;
		refreshMenu();
		g_RCInput->postMsg((neutrino_msg_t) CRCInput::RC_up, 0);
		return res;
	}

	map<string, struct pkg>::iterator it = pkg_map.find(actionKey);
	if (it != pkg_map.end()) {
		if (parent)
			parent->hide();
		string force = "";
		if (it->second.installed && !it->second.upgradable) {
			char l[200];
			snprintf(l, sizeof(l), g_Locale->getText(LOCALE_OPKG_MESSAGEBOX_REINSTALL), actionKey.c_str());
			l[sizeof(l) - 1] = 0;
			if (ShowMsg(LOCALE_OPKG_TITLE, l, CMessageBox::mbrCancel, CMessageBox::mbYes | CMessageBox::mbCancel) == CMessageBox::mbrCancel)
				return res;
			force = "--force-reinstall ";
		}

		//check package size...cancel installation if size check failed
		if (!checkSize(actionKey)){
			DisplayErrorMessage(g_Locale->getText(LOCALE_OPKG_MESSAGEBOX_SIZE_ERROR));
		}
		else{
			int r = execCmd(pkg_types[OM_INSTALL] + force + actionKey, true, true);
			if (r)
				showError(g_Locale->getText(LOCALE_OPKG_FAILURE_INSTALL), strerror(errno), pkg_types[OM_INSTALL] + force + actionKey);
			else
				installed = true;
		}

		refreshMenu();
	}
	return res;
}

bool COPKGManager::checkSize(const string& pkg_name)
{
	//get package size
	string s_pkgsize = getPkgInfo(pkg_name, "Size");
	std::istringstream s(s_pkgsize);
	u_int64_t pkg_size;
	s >> pkg_size;

	//get available size
	//TODO: Check writability!
	struct statfs root_fs;
	statfs("/",&root_fs);
	u_int64_t free_size = root_fs.f_bfree*root_fs.f_bsize;
	dprintf(DEBUG_INFO,  "[COPKGManager] [%s - %d] Package: %s [package size=%lld (free size: %lld)]\n", __func__, __LINE__, pkg_name.c_str(), pkg_size, free_size);

	//only for sure, it's more secure for users to abort installation if is available size too small
	//TODO: Package size is not really the same like required/recommended size, because of unknown compression factor, some possible options like cache, different tmp-dir size eg. are still not considered.
	u_int64_t rec_size = pkg_size/2*3;
	if (free_size < rec_size){
		dprintf(DEBUG_NORMAL,  "[COPKGManager] [%s - %d]  WARNING: size check freesize=%lld required size=%lld (recommended: %lld)\n", __func__, __LINE__, free_size, pkg_size, rec_size);
		return false;
	}
	return true;
}


#define COPKGManagerFooterButtonCount 3
static const struct button_label COPKGManagerFooterButtons[COPKGManagerFooterButtonCount] = {
	{ NEUTRINO_ICON_BUTTON_YELLOW, LOCALE_OPKG_BUTTON_EXPERT_ON },
	{ NEUTRINO_ICON_BUTTON_INFO_SMALL, LOCALE_OPKG_BUTTON_INFO },
	{ NEUTRINO_ICON_BUTTON_OKAY,	   LOCALE_OPKG_BUTTON_INSTALL }
};
#define COPKGManagerFooterButtonCountExpert 4
static const struct button_label COPKGManagerFooterButtonsExpert[COPKGManagerFooterButtonCountExpert] = {
	{ NEUTRINO_ICON_BUTTON_YELLOW, LOCALE_OPKG_BUTTON_EXPERT_OFF },
	{ NEUTRINO_ICON_BUTTON_INFO_SMALL, LOCALE_OPKG_BUTTON_INFO },
	{ NEUTRINO_ICON_BUTTON_OKAY,	   LOCALE_OPKG_BUTTON_INSTALL },
	{ NEUTRINO_ICON_BUTTON_BLUE, LOCALE_OPKG_BUTTON_UNINSTALL }
};

/* TODO: this should go into a config file... */
static std::string bad_pattern[] = {
	"-dev$",
	"-doc$",
	"-dbg$",
	"-ptest$",
	"-staticdev$",
	"-locale-",
	"-charmap-",
	"-gconv-",
	"-localedata-",
	"^locale-base-",
	"^perl-module-",
	""
};

bool COPKGManager::badpackage(std::string &s)
{
	int i;
	for (i = 0; !bad_pattern[i].empty(); i++)
	{
		std::string p = bad_pattern[i];
		size_t patlen = p.length() - 1;
		/* poor man's regex :-) only supported are "^" and "$" */
		if (p.substr(patlen, 1) == "$") { /* match at end */
			if (s.rfind(p.substr(0, patlen)) == (s.length() - patlen))
				return true;
		} else if (p.substr(0, 1) == "^") { /* match at beginning */
			if (s.find(p.substr(1)) == 0)
				return true;
		} else { /* match everywhere */
			if (s.find(p) != std::string::npos)
				return true;
		}
	}
	return false;
}

void COPKGManager::updateMenu()
{
	bool upgradesAvailable = false;
	getPkgData(OM_LIST_INSTALLED);
	getPkgData(OM_LIST_UPGRADEABLE);
	for (map<string, struct pkg>::iterator it = pkg_map.begin(); it != pkg_map.end(); it++) {
		if (badpackage(it->second.name))
			continue;
		it->second.forwarder->iconName_Info_right = "";
		it->second.forwarder->setActive(true);
		if (it->second.upgradable) {
			it->second.forwarder->iconName_Info_right = NEUTRINO_ICON_WARNING;
			upgradesAvailable = true;
		} else if (it->second.installed) {
			it->second.forwarder->iconName_Info_right = NEUTRINO_ICON_CHECKMARK;
			it->second.forwarder->setActive(expert_mode);
		}
	}

	upgrade_forwarder->setActive(upgradesAvailable);

	if (expert_mode){
		menu->setFooter(COPKGManagerFooterButtonsExpert, COPKGManagerFooterButtonCountExpert);
	}
	else{
		menu->setSelected(2); //back-item
		menu->setFooter(COPKGManagerFooterButtons, COPKGManagerFooterButtonCount);
	}
}

bool COPKGManager::checkUpdates(const std::string & package_name, bool show_progress)
{
	if (!hasOpkgSupport())
		return false;

	doUpdate();

	bool ret = false;

	getPkgData(OM_LIST);
	getPkgData(OM_LIST_UPGRADEABLE);

	size_t i = 0;
	CProgressWindow status;
	status.showHeader(false);

	if (show_progress){
		status.paint();
		status.showStatus(i);
	}

	for (map<string, struct pkg>::iterator it = pkg_map.begin(); it != pkg_map.end(); it++){
		dprintf(DEBUG_INFO,  "[COPKGManager] [%s - %d]  Update check for...%s\n", __func__, __LINE__, it->second.name.c_str());
		if (show_progress){
			status.showStatusMessageUTF(it->second.name);
			status.showStatus(100*i /  pkg_map.size());
		}

		if (it->second.upgradable){
			dprintf(DEBUG_INFO,  "[COPKGManager] [%s - %d]  Update packages available for...%s\n", __func__, __LINE__, it->second.name.c_str());
			if (!package_name.empty() && package_name == it->second.name){
				ret = true;
				break;
			}else
				ret = true;
		}
		i++;
	}

	if (show_progress){
		status.showGlobalStatus(100);
		status.showStatusMessageUTF(g_Locale->getText(LOCALE_FLASHUPDATE_READY)); // UTF-8
		status.hide();
	}

	pkg_map.clear();

	return ret;
}

int COPKGManager::doUpdate()
{
	int r = execCmd(pkg_types[OM_UPDATE]);
	if (r == -1) {
		string msg = string(g_Locale->getText(LOCALE_OPKG_FAILURE_UPDATE)) + "\n" + err_msg;
		DisplayErrorMessage(msg.c_str());
		return r;
	}
	return 0;
}

void COPKGManager::refreshMenu() {
	list_installed_done = false,
	list_upgradeable_done = false;
	updateMenu();
}

int COPKGManager::showMenu()
{
	installed = false;
	if (checkUpdates())
		DisplayInfoMessage(g_Locale->getText(LOCALE_OPKG_MESSAGEBOX_UPDATES_AVAILABLE));

	getPkgData(OM_LIST);
	getPkgData(OM_LIST_UPGRADEABLE);

	menu = new CMenuWidget(g_Locale->getText(LOCALE_SERVICEMENU_UPDATE), NEUTRINO_ICON_UPDATE, width, MN_WIDGET_ID_SOFTWAREUPDATE);
	menu->addIntroItems(LOCALE_OPKG_TITLE, NONEXISTANT_LOCALE, CMenuWidget::BTN_TYPE_BACK, CMenuWidget::BRIEF_HINT_YES);

	//upgrade all installed packages
	upgrade_forwarder = new CMenuForwarder(LOCALE_OPKG_UPGRADE, true, NULL , this, pkg_types[OM_UPGRADE].c_str(), CRCInput::RC_red);
	upgrade_forwarder->setHint(NEUTRINO_ICON_HINT_SW_UPDATE, LOCALE_MENU_HINT_OPKG_UPGRADE);
	menu->addItem(upgrade_forwarder);

	//select and install local package
	CMenuForwarder *local;
	local = new CMenuForwarder(LOCALE_OPKG_INSTALL_LOCAL_PACKAGE, true, NULL, this, "local_package", CRCInput::RC_green);
	local->setHint(NEUTRINO_ICON_HINT_SW_UPDATE, LOCALE_MENU_HINT_OPKG_INSTALL_LOCAL_PACKAGE);
	menu->addItem(local);

	menu->addItem(GenericMenuSeparatorLine);

	menu_offset = menu->getItemsCount();

	menu->addKey(CRCInput::RC_info, this, "rc_info");
	menu->addKey(CRCInput::RC_blue, this, "rc_blue");
	menu->addKey(CRCInput::RC_yellow, this, "rc_yellow");

	pkg_vec.clear();
	for (map<string, struct pkg>::iterator it = pkg_map.begin(); it != pkg_map.end(); it++) {
		if (badpackage(it->second.name))
			continue;
		it->second.forwarder = new CMenuForwarder(it->second.desc, true, NULL , this, it->second.name.c_str());
		it->second.forwarder->setHint("", it->second.desc);
		menu->addItem(it->second.forwarder);
		pkg_vec.push_back(&it->second);
	}

	updateMenu();

	int res = menu->exec(NULL, "");

	menu->hide ();

	//handling after successful installation
	string exit_action = "";
	if (!has_err && installed){
		/*!
			Show a success message only if restart/reboot is required and user should decide what to do or not.
			NOTE: marker file should be generated by opkg package itself (eg. with preinstall scripts),
			so it's controlled by the package maintainer!
		*/
		//restart neutrino: user decision
		if(!access( "/tmp/.restart", F_OK)){
			int msg = ShowMsg(LOCALE_OPKG_TITLE, g_Locale->getText(LOCALE_OPKG_SUCCESS_INSTALL), CMessageBox::mbrNo,
			CMessageBox::mbYes | CMessageBox::mbNo,
			NEUTRINO_ICON_QUESTION,
			width);
			if (msg == CMessageBox::mbrYes)
				exit_action = "restart";
		}
		//restart neutrino: forced
		if (!access( "/tmp/.force_restart", F_OK))
			exit_action = "restart";
		//reboot stb: forced
		if (!access( "/tmp/.reboot", F_OK))
			exit_action = "reboot";
	}

	delete menu;

	if (!exit_action.empty())
		CNeutrinoApp::getInstance()->exec(NULL, exit_action);

	return res;
}

bool COPKGManager::hasOpkgSupport()
{
	string deps[] = {"/etc/opkg/opkg.conf", "/var/lib/opkg"};

	if (find_executable(OPKG_CL).empty()) {
		dprintf(DEBUG_NORMAL, "[COPKGManager] [%s - %d]" OPKG_CL " executable not found\n", __func__, __LINE__);
		return false;
	}
	for(size_t i=0; i<sizeof(deps)/sizeof(deps[0]) ;i++){
		if(access(deps[i].c_str(), R_OK) !=0) {
			dprintf(DEBUG_NORMAL,  "[COPKGManager] [%s - %d] %s not found\n", __func__, __LINE__, deps[i].c_str());
			return false;
		}
	}

	return true;
}

void COPKGManager::getPkgData(const int pkg_content_id)
{
	dprintf(DEBUG_INFO, "[COPKGManager] [%s - %d] executing %s\n", __func__, __LINE__, pkg_types[pkg_content_id].c_str());

	switch (pkg_content_id) {
		case OM_LIST:
			pkg_map.clear();
			list_installed_done = false;
			list_upgradeable_done = false;
			break;
		case OM_LIST_INSTALLED:
			if (list_installed_done)
				return;
			list_installed_done = true;
			for (map<string, struct pkg>::iterator it = pkg_map.begin(); it != pkg_map.end(); it++)
				it->second.installed = false;
			break;
		case OM_LIST_UPGRADEABLE:
			if (list_upgradeable_done)
				return;
			list_upgradeable_done = true;
			for (map<string, struct pkg>::iterator it = pkg_map.begin(); it != pkg_map.end(); it++)
				it->second.upgradable = false;
			break;
	}

	pid_t pid = 0;
	FILE *f = my_popen(pid, pkg_types[pkg_content_id].c_str(), "r");
	if (!f) {
		showError("Internal Error", strerror(errno), pkg_types[pkg_content_id]);
		return;
	}

	char buf[256];

	while (fgets(buf, sizeof(buf), f))
	{
		if (buf[0] == ' ')
			continue; /* second, third, ... line of description will not be shown anyway */
		std::string line(buf);
		trim(line);

		string name = getBlankPkgName(line);
		if (name.empty())
			continue;

		switch (pkg_content_id) {
			case OM_LIST: {
				pkg_map[name] = pkg(name, line, line);
				break;
			}
			case OM_LIST_INSTALLED: {
				map<string, struct pkg>::iterator it = pkg_map.find(name);
				if (it != pkg_map.end())
					it->second.installed = true;
				break;
			}
			case OM_LIST_UPGRADEABLE: {
				map<string, struct pkg>::iterator it = pkg_map.find(name);
				if (it != pkg_map.end())
					it->second.upgradable = true;
				break;
			}
			default:
				fprintf(stderr, "%s %s %d: unrecognized content id %d\n", __FILE__, __func__, __LINE__, pkg_content_id);
				break;
		}
	}

	fclose(f);
}

string COPKGManager::getBlankPkgName(const string& line)
{
	dprintf(DEBUG_INFO,  "[COPKGManager] [%s - %d]  line: %s\n", __func__, __LINE__, line.c_str());

	//check for error relevant contents and return an empty string if found
	size_t pos0 = line.find("Collected errors:");
	size_t pos01 = line.find(" * ");
	if (pos0 != string::npos || pos01 != string::npos)
		return "";

	//split line and use name as return value
	size_t pos1 = line.find(" ");
	if (pos1 != string::npos)
		return line.substr(0, pos1);

	return "";
}

string COPKGManager::getPkgInfo(const string& pkg_name, const string& pkg_key)
{
	tmp_str.clear();
	execCmd(pkg_types[OM_INFO] + pkg_name, false, true);
	dprintf(DEBUG_INFO,  "[COPKGManager] [%s - %d]  [data: %s]\n", __func__, __LINE__, tmp_str.c_str());

	return getKeyInfo(tmp_str, pkg_key, ":");
}

string COPKGManager::getKeyInfo(const string& input, const std::string& key, const string& delimiters)
{
	string s = input;
	size_t pos1 = s.find(key);
	if (pos1 != string::npos){
		size_t pos2 = s.find(delimiters, pos1)+ delimiters.length();
		if (pos2 != string::npos){
			size_t pos3 = s.find("\n", pos2);
			if (pos3 != string::npos){
				string ret = s.substr(pos2, pos3-pos2);
				return trim(ret, " ");
			}
			else
				dprintf(DEBUG_INFO, "[COPKGManager] [%s - %d]  Error: [key: %s] missing end of line...\n", __func__, __LINE__, key.c_str());
		}
	}
	return "";
}

int COPKGManager::execCmd(const char *cmdstr, bool verbose, bool acknowledge)
{
	fprintf(stderr, "execCmd(%s)\n", cmdstr);
	string cmd = string(cmdstr);
	int res = 0;
	has_err = false;
	tmp_str.clear();
	err_msg = "";
	if (verbose) {
		sigc::slot1<void, string&> sl;
		sl = sigc::mem_fun(*this, &COPKGManager::handleShellOutput);
		CShellWindow shell(cmd, (verbose ? CShellWindow::VERBOSE : 0) | (acknowledge ? CShellWindow::ACKNOWLEDGE_MSG : 0), &res, false);
		shell.OnShellOutputLoop.connect(sl);
		shell.exec();
	} else {
		cmd += " 2>&1";
		pid_t pid = 0;
		FILE *f = my_popen(pid, cmd.c_str(), "r");
		if (!f) {
			showError("OPKG-Error!", strerror(errno), cmd);
			return -1;
		}
		char buf[256];
		while (fgets(buf, sizeof(buf), f))
		{
			string line(buf);
			trim(line);
			dprintf(DEBUG_INFO,  "[COPKGManager] [%s - %d]  %s [error %d]\n", __func__, __LINE__, line.c_str(), has_err);
			handleShellOutput(line);
		}
		fclose(f);
	}
	if (has_err){
		return -1;
	}

	return res;
}

void COPKGManager::handleShellOutput(string& cur_line)
{
	size_t pos2 = cur_line.find("Collected errors:");
	if (pos2 != string::npos)
		has_err = true;

	//check for collected errors and build a message for screen if errors available
	if (has_err){
		dprintf(DEBUG_NORMAL,  "[COPKGManager] [%s - %d]  result: %s\n", __func__, __LINE__, cur_line.c_str());

		//trivial errors:
		/*duplicate option cache: option is defined in OPKG_CL_CONFIG_OPTIONS,
		 * NOTE: if found first cache option in the opkg.conf file, this will be preferred and it's not really an error!
		*/
		if (cur_line.find("Duplicate option cache") != string::npos){
			dprintf(DEBUG_NORMAL,  "[COPKGManager] [%s - %d]  WARNING: Duplicate option cache, please check opkg config file!\n", __func__, __LINE__);
			has_err = false;
		}

		//find obvious errors
		//download error:
		if (cur_line.find("opkg_download:") != string::npos){
			err_msg += "Network error! Please check your network connection!\n";
			has_err = true;
		}
		//install errors:
		if (cur_line.find("opkg_install_pkg") != string::npos){
			err_msg += "Update not possible!\n";
			has_err = true;
		}
		if (cur_line.find("opkg_install_cmd") != string::npos){
			err_msg += "Cannot install package!\n";
			has_err = true;
		}
		if (cur_line.find("No space left on device") != string::npos){
			err_msg += "Not enough space available!\n";
			has_err = true;
		}
		if (has_err)
			return;

		//add unknown errors:
		size_t pos1 = cur_line.find(" * ");
		if (pos1 != string::npos){
			string str = cur_line.substr(pos1, cur_line.length()-pos1);
			err_msg += str.replace(pos1, 3,"") + "\n";
			has_err = true;
		}
		if (has_err)
			return;
	}
	if (!has_err)
		tmp_str += cur_line + "\n";
}

void COPKGManager::showError(const char* local_msg, char* err_message, const string& command)
{
	string msg = local_msg ? string(local_msg) + "\n" : "";
	msg += err_msg + "\n";
	msg += string(err_message) + ":\n";
	msg += command;
	DisplayErrorMessage(msg.c_str());
}

bool COPKGManager::installPackage(const std::string& pkg_name)
{
	int r = execCmd(pkg_types[OM_INSTALL] + pkg_name, true, true);

	if (r){
		dprintf(DEBUG_NORMAL,  "[COPKGManager] [%s - %d]  error[%d]: %s\n", __func__, __LINE__, errno, strerror(errno));
// 		showError(g_Locale->getText(LOCALE_OPKG_FAILURE_INSTALL), strerror(errno), pkg_name);
		return false;
	}
	else
		installed = true;

	return true;
}
