Package.describe({
	name: 'rocketchat:ui-flextab',
	version: '0.1.0',
	// Brief, one-line summary of the package.
	summary: '',
	// URL to the Git repository containing the source code for this package.
	git: '',
	// By default, Meteor will default to using README.md for documentation.
	// To avoid submitting documentation, set this field to null.
	documentation: 'README.md'
});

Package.onUse(function(api) {
	api.use([
		'mongo',
		'ecmascript',
		'templating',
		'coffeescript',
		'underscore',
		'rocketchat:lib'
	]);

	api.use('rocketchat:ui');

	api.addFiles('flex-tab/flexTabBar.html', 'client');
	api.addFiles('flex-tab/tabs/membersList.html', 'client');
	api.addFiles('flex-tab/tabs/messageSearch.html', 'client');
	api.addFiles('flex-tab/tabs/uploadedFilesList.html', 'client');
	api.addFiles('flex-tab/tabs/userEdit.html', 'client');
	api.addFiles('flex-tab/tabs/userInfo.html', 'client');

	api.addFiles('flex-tab/flexTabBar.coffee', 'client');
	api.addFiles('flex-tab/tabs/membersList.coffee', 'client');
	api.addFiles('flex-tab/tabs/messageSearch.coffee', 'client');
	api.addFiles('flex-tab/tabs/uploadedFilesList.coffee', 'client');
	api.addFiles('flex-tab/tabs/userEdit.coffee', 'client');
	api.addFiles('flex-tab/tabs/userInfo.coffee', 'client');

});
